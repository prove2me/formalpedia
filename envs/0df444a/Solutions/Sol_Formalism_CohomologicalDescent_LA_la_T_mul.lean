-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_T_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:02:36.127829+00:00
-- url     : https://prove2.me/submissions/26bc2989-1340-4d46-b679-ee666191fde4

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_monLat_mul
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution {c d c' d' : ℕ} {f f' : MvPolynomial (Fin 2 × Fin 2) ℤ} (hf : f ∈ detPowMulMonomialSpan c d)
    (hf' : f' ∈ detPowMulMonomialSpan c' d') : f * f' ∈ detPowMulMonomialSpan (c + c') (d + d') := by
  rw [detPowMulMonomialSpan] at hf hf' ⊢
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hf
  obtain ⟨u', hu', rfl⟩ := Submodule.mem_map.mp hf'
  refine Submodule.mem_map.mpr ⟨u * u', la_monLat_mul ℤ (0 : Fin 2) hu hu', ?_⟩
  simp only [LinearMap.mulLeft_apply]
  ring
end Formalism.CohomologicalDescent.LA
