/- Copyright (c) 2022 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
----------------
# The Covariant Yoneda Lemma in Lean4
-/


import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Yoneda

open CategoryTheory
open Opposite


/- 
Here's minimally eequired category theory API from MathLib4 to construct, for any copresheaf `F` on a category `𝓒` the isomorphism of types `(よ A ⟶ F) ≃ F.obj A`. 
-/

#print Functor
#print NatTrans
#check coyoneda 
#check coyoneda.obj 
#check coyoneda.map

universe u
variable {𝓒 : Type u} [Category 𝓒] -- Category `𝓒`
variable (A : 𝓒) -- An object `A` of category `𝓒`
variable (F : 𝓒 ⥤ Type v₁) -- A co-presheaf `F` on `𝓒`
variable (θ : coyoneda.obj (op A) ⟶  F) -- A natural transformation `θ` from the corepresentable copresheaf to `F`. Note that `op A` is an object of the oppposite category `𝓒ᵒᵖ`.


def iso_of_hom_iso (X Y : 𝓒) (h : yoneda.obj X ≅ yoneda.obj Y) : X ≅ Y where
  hom := h.hom.app (op X) (𝟙 X)
  inv := h.inv.app (op Y) (𝟙 Y)


variable (F : 𝓒 ⥤ Type v₁) (A : 𝓒) (θ : coyoneda.obj (op A) ⟶  F)

/-
Consider the following commutative square:
   
```   
        θ.app A
𝓒(A,A) --------> F.obj A
  |                |
  |                |
  |                |
  v                v
𝓒(A,X) --------> F.obj X
        θ.app X
```

where the vertical arrows are given by `coyoneda.map f` and .

where the horizontal arrows are given by `θ.app` and the vertical arrows are given by `(coyoneda.obj (op A)).map f` and `F.map f`.

-/



#check coyoneda.map 

notation:75  "よ" arg:75  => coyoneda.obj (op arg)

@[simp]
lemma coyoneda_obj : よ A = coyoneda.obj (op A)  := rfl

--@[simp]
@[aesop forward safe]
lemma cov_naturality_fibrewise : 
  ∀ (f : A ⟶ X),  (θ.app X) f  = (F.map f) (θ.app A (𝟙 A)) := 
by 
  intro f
  have this : f = (よ A).map f (𝟙 A):= by simp
  conv => 
  -- focusing on simplifying the left hand side by substituting the equality above 
    lhs 
    rw [this]
    change ((よ A).map f ≫ θ.app X) (𝟙 A)
  -- out of the conv mode  
  rw [NatTrans.naturality]
  rfl
  


def YonedaCovariant : 
  (よ A ⟶ F) ≃ F.obj A where
    toFun := fun α => α.app A (𝟙 A)
    invFun := fun u => {
                           app := fun X => fun f => (F.map f) u,
                           naturality := by aesop_cat
                        }
    left_inv := by aesop_cat
    right_inv := by aesop_cat

/-
Exercise: Prove the contravariant version of the Yoneda lemma.
-/






