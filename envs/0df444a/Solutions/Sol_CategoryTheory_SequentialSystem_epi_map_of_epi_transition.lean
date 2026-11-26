-- Prove2me | solution 1 for CategoryTheory.SequentialSystem.epi_map_of_epi_transition
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:42:15.169794+00:00
-- url     : https://prove2.me/submissions/ba1ef9ca-caa2-4dc1-b874-2b336b1216a9

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

section Transition


/-- If the successive transition maps of an inverse system are epimorphisms, so are all
the maps `F.obj (op n) ⟶ F.obj (op m)` for `m ≤ n`. -/
lemma epi_map_of_epi_transition (F : ℕᵒᵖ ⥤ C)
    (hF : ∀ n, Epi (transition F n)) {m n : ℕ} (hmn : m ≤ n) :
    Epi (F.map (homOfLE hmn).op) := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := Nat.le_zero.mp hmn
    rw [Subsingleton.elim (homOfLE hmn) (𝟙 (0 : ℕ)), op_id, F.map_id]
    infer_instance
  | succ n ih =>
    by_cases hm : m = n + 1
    · subst hm
      rw [Subsingleton.elim (homOfLE hmn) (𝟙 (n + 1 : ℕ)), op_id, F.map_id]
      infer_instance
    · have hmn' : m ≤ n := Nat.lt_succ_iff.mp (lt_of_le_of_ne hmn hm)
      rw [Subsingleton.elim (homOfLE hmn) (homOfLE hmn' ≫ homOfLE (Nat.le_succ n)), op_comp,
        F.map_comp]
      haveI := hF n
      haveI := ih hmn'
      exact epi_comp _ _


end Transition


end SequentialSystem
end CategoryTheory


theorem solution.{sol_u1, sol_u2} : type_of% @CategoryTheory.SequentialSystem.epi_map_of_epi_transition.{sol_u1, sol_u2} := @CategoryTheory.SequentialSystem.epi_map_of_epi_transition.{sol_u1, sol_u2}
