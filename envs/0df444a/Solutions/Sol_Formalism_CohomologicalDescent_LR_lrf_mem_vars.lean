-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrf_mem_vars
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:14.995108+00:00
-- url     : https://prove2.me/submissions/1c14f831-5e3b-4e20-ab95-f8ed135dcc4e

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_mem_L

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (v : Fin r × Fin n) :
    v ∈ (lrf_L r n).map (·.2.2) ↔ v.2.val < v.1.val := by
  rw [List.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    rw [lrf_mem_L] at hl
    rw [hl.2.2]
    exact hl.2.1
  · intro h
    refine ⟨(⟨v.2.val, lt_trans h v.1.isLt⟩, v.1, v), ?_, rfl⟩
    rw [lrf_mem_L]
    exact ⟨rfl, h, rfl⟩
end Formalism.CohomologicalDescent.LR
