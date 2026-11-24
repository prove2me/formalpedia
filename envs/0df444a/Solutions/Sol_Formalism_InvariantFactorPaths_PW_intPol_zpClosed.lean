-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.intPol_zpClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:50:25.357391+00:00
-- url     : https://prove2.me/submissions/d0d4de50-5f0e-40d9-9ff4-adfe771e621a

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatData
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_mem_intPol_addSubgroup

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
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (σ : Type) : ZpClosed p (IntPol p σ).toAddSubgroup := by
  intro c hc x hx
  rw [mem_intPol_addSubgroup] at hx ⊢
  intro m
  rw [coeff_smul, smul_eq_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (hx m)
end Formalism.InvariantFactorPaths.PW
