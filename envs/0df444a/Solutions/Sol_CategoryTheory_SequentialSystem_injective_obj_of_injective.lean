-- Prove2me | solution 1 for CategoryTheory.SequentialSystem.injective_obj_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:42:18.72242+00:00
-- url     : https://prove2.me/submissions/a97a2a13-9f9c-41af-bedf-2aa16c7b5e1f

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


/-- Naturality of `extendSystemHomEquiv` in the object. -/
lemma extendSystemHomEquiv_map_comp {M M' : C} (h : M ⟶ M')
    (φ : extendSystem n M' ⟶ F) :
    extendSystemHomEquiv n M F (extendSystemMap n h ≫ φ) =
      h ≫ extendSystemHomEquiv n M' F φ := by
  have e : (extendSystemMap n h).app (op n) =
      eqToHom (if_pos (le_refl n)) ≫ h ≫ eqToHom (if_pos (le_refl n)).symm := dif_pos le_rfl
  simp only [extendSystemHomEquiv_apply, NatTrans.comp_app, e, Category.assoc]
  simp


end Extend


section Injective

variable [HasZeroMorphisms C] [HasZeroObject C]


/-- The objects of an injective inverse system are injective. -/
theorem injective_obj_of_injective (I : ℕᵒᵖ ⥤ C) [Injective I] (n : ℕ) :
    Injective (I.obj (op n)) := by
  constructor
  intro X Y g f hf
  haveI := hf
  have h := extendSystemHomEquiv_map_comp n I f
    (Injective.factorThru ((extendSystemHomEquiv n X I).symm g) (extendSystemMap n f))
  rw [Injective.comp_factorThru, Equiv.apply_symm_apply] at h
  exact ⟨_, h.symm⟩

end Injective

end SequentialSystem
end CategoryTheory


theorem solution.{sol_u1, sol_u2} : type_of% @CategoryTheory.SequentialSystem.injective_obj_of_injective.{sol_u1, sol_u2} := @CategoryTheory.SequentialSystem.injective_obj_of_injective.{sol_u1, sol_u2}
