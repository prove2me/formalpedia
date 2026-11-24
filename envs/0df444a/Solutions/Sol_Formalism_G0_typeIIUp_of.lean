-- Prove2me | solution 1 for Formalism.G0.typeIIUp_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:21.543637+00:00
-- url     : https://prove2.me/submissions/a8f311cc-5aff-4b0c-a4d0-f931719b7566

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIUp
import Theorems.Thm_Formalism_G0_TypeIIUpP_arith
import Theorems.Thm_Formalism_G0_TypeIIUpP_countBelow_eq
import Theorems.Thm_Formalism_G0_TypeIIUpP_countAbove_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
namespace Formalism.G0
theorem _root_.solution (hS : SubspaceCount) : TypeIIUp := by
  intro F P Q _ _ _ _ _ _ _ _ f N g j hP hQ
  haveI : Module.Finite F P := Module.Finite.of_finite
  haveI : Module.Finite F Q := Module.Finite.of_finite
  haveI := TypeIIUpP.finite_quot (LinearMap.range f)
  obtain ⟨ρ, hρ⟩ : ∃ ρ, Module.finrank F (LinearMap.range f) = ρ := ⟨_, rfl⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hquot := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  rw [hρ, hP] at hrn
  rw [hρ, hQ] at hquot
  have hK : ∀ l, Nat.card {U : Submodule F P // U ≤ LinearMap.ker f ∧ Module.finrank F U + (j - l) = N} =
      if j - l ≤ N then gaussBinom (Fintype.card F) (N - ρ) (N - (j - l)) else 0 := by
    intro l
    split_ifs with hl
    · rw [Nat.card_congr (Equiv.subtypeEquivRight
          (q := fun U : Submodule F P => U ≤ LinearMap.ker f ∧ Module.finrank F U = N - (j - l))
          (fun U => and_congr_right (fun _ => ⟨fun h => by omega, fun h => by omega⟩)))]
      show countBelow (LinearMap.ker f) (N - (j - l)) = _
      rw [TypeIIUpP.countBelow_eq, hS]
      congr 1
      omega
    · rw [Nat.card_eq_zero]
      left
      constructor
      rintro ⟨U, _, hU⟩
      omega
  have hA : countAbove (LinearMap.range f) j =
      if ρ ≤ j then gaussBinom (Fintype.card F) (N + g - ρ) (j - ρ) else 0 := by
    rw [TypeIIUpP.countAbove_eq, hS]
    have hq : Module.finrank F (Q ⧸ LinearMap.range f) = N + g - ρ := by omega
    rw [hq, hρ]
  rw [hA]
  simp only [hK]
  have key := TypeIIUpP.arith (Fintype.card F) N g j ρ (by omega)
  exact_mod_cast key
end Formalism.G0
