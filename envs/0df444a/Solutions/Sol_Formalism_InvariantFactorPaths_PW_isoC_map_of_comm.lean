-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.isoC_map_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:10:39.220475+00:00
-- url     : https://prove2.me/submissions/9b88d3d2-b280-4acf-8d04-004e3c674c51

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_isoC_stable
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_hwc_le_isoC
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_hwc_map_of_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x, A (glAct p LL j c d x) = glAct p LL j c d (A x)) (la : Fin r → ℤ) :
    ∀ x ∈ IsoC p LL j Cs la, A x ∈ IsoC p LL j Cs la := by
  have hle : IsoC p LL j Cs la ≤ (IsoC p LL j Cs la).comap A := by
    conv_lhs => rw [IsoC]
    refine sInf_le ⟨?_, ?_⟩
    · intro x hx
      exact hwc_le_isoC LL j Cs la (hwc_map_of_comm LL j Cs A hA la x hx)
    · intro c hc d hd x hx
      rw [Submodule.mem_comap] at hx ⊢
      rw [hA c hc d hd]
      exact isoC_stable LL j Cs la c hc d hd _ hx
  exact fun x hx => hle hx
end Formalism.InvariantFactorPaths.PW
