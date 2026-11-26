-- Prove2me | solution 1 for CategoryTheory.SequentialSystem.isSplitEpi_transition_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:42:20.010969+00:00
-- url     : https://prove2.me/submissions/56513f97-f988-4922-8528-b0c6ee4ca3ac

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem_Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

/-!
# Inverse systems indexed by `ℕᵒᵖ`

We study functors `F : ℕᵒᵖ ⥤ C` ("inverse systems") in a category `C` with zero object
and zero morphisms. The *transition maps* of `F` are the maps
`F.obj (op (n + 1)) ⟶ F.obj (op n)`.

The key results concern injective objects of the functor category:

- `CategoryTheory.SequentialSystem.isSplitEpi_transition_of_injective`: the transition
  maps of an injective inverse system are split epimorphisms.
- `CategoryTheory.SequentialSystem.injective_obj_of_injective`: the objects of an
  injective inverse system are injective.

Both are proved using the "extension by zero" systems `extendSystem n M`, which take the
value `M` in degrees `≤ n` (with identity transitions) and `0` above, together with the
natural identification `(extendSystem n M ⟶ F) ≃ (M ⟶ F.obj (op n))` and the
monomorphism `extendSystem n M ⟶ extendSystem (n + 1) M`.

We also record stability properties of the class of systems with epimorphic transition
maps.
-/

universe w v v' u u'

open CategoryTheory Limits Opposite

open scoped ZeroObject

namespace CategoryTheory
namespace SequentialSystem

variable {C : Type u} [Category.{v} C]


section Extend

variable [HasZeroMorphisms C] [HasZeroObject C]


variable (n : ℕ) (M : C) (F : ℕᵒᵖ ⥤ C)


/-- Compatibility of `extendSystemHomEquiv` with precomposition by `extendSystemι`:
restriction along `ι` corresponds to postcomposition with the transition map. -/
lemma extendSystemHomEquiv_ι_comp (ψ : extendSystem (n + 1) M ⟶ F) :
    extendSystemHomEquiv n M F (extendSystemι n M ≫ ψ) =
      extendSystemHomEquiv (n + 1) M F ψ ≫ transition F n := by
  have hι : (extendSystemι n M).app (op n) =
      eqToHom (if_pos (le_refl n)) ≫ eqToHom (if_pos ((le_refl n).trans (Nat.le_succ n))).symm :=
    dif_pos le_rfl
  have hmap : (extendSystem (n + 1) M).map (homOfLE (Nat.le_succ n)).op =
      eqToHom (if_pos (le_refl (n + 1))) ≫ eqToHom (if_pos (Nat.le_succ n)).symm :=
    dif_pos le_rfl
  have hnat : ψ.app (op (n + 1)) ≫ transition F n =
      eqToHom (if_pos (le_refl (n + 1))) ≫ eqToHom (if_pos (Nat.le_succ n)).symm ≫
        ψ.app (op n) := by
    rw [← Category.assoc, ← hmap]
    exact (ψ.naturality (homOfLE (Nat.le_succ n)).op).symm
  simp only [extendSystemHomEquiv_apply, NatTrans.comp_app, hι, Category.assoc]
  rw [hnat]
  simp


end Extend


section Injective

variable [HasZeroMorphisms C] [HasZeroObject C]

/-- The transition maps of an injective inverse system are split epimorphisms. -/
theorem isSplitEpi_transition_of_injective (I : ℕᵒᵖ ⥤ C) [Injective I] (n : ℕ) :
    IsSplitEpi (transition I n) := by
  have h := extendSystemHomEquiv_ι_comp n (I.obj (op n)) I
    (Injective.factorThru ((extendSystemHomEquiv n (I.obj (op n)) I).symm (𝟙 (I.obj (op n))))
      (extendSystemι n (I.obj (op n))))
  rw [Injective.comp_factorThru, Equiv.apply_symm_apply] at h
  exact IsSplitEpi.mk' ⟨_, h.symm⟩


end Injective

end SequentialSystem
end CategoryTheory


theorem solution.{sol_u1, sol_u2} : type_of% @CategoryTheory.SequentialSystem.isSplitEpi_transition_of_injective.{sol_u1, sol_u2} := @CategoryTheory.SequentialSystem.isSplitEpi_transition_of_injective.{sol_u1, sol_u2}
