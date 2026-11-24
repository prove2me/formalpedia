-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrf_mem_L
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:00.51822+00:00
-- url     : https://prove2.me/submissions/e0063a96-1877-4078-8986-7181117ae80a

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_mem_col
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (l : Fin r × Fin r × (Fin r × Fin n)) :
    l ∈ lrf_L r n ↔ l.1.val = l.2.2.2.val ∧ l.2.2.2.val < l.2.1.val ∧ l.2.2.1 = l.2.1 := by
  unfold lrf_L
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨s, -, hs⟩
    rw [lrf_mem_col] at hs
    obtain ⟨h1, h2, h3⟩ := hs
    rw [h3]
    exact ⟨h1, h2, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨l.2.2.2, by simp, ?_⟩
    rw [lrf_mem_col]
    exact ⟨h1, h2, Prod.ext h3 rfl⟩
end Formalism.CohomologicalDescent.LR
