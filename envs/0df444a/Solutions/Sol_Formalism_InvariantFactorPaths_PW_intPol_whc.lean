-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.intPol_whc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:50:24.724189+00:00
-- url     : https://prove2.me/submissions/b77055fa-9dd9-4238-bb3e-7dd3df72b1c1

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
theorem _root_.solution {σ M : Type} [AddCommMonoid M] (w : σ → M) (μ : M) (x : MvPolynomial σ ℚ_[p])
    (hx : x ∈ (IntPol p σ).toAddSubgroup) :
    weightedHomogeneousComponent w μ x ∈ (IntPol p σ).toAddSubgroup := by
  classical
  rw [mem_intPol_addSubgroup] at hx ⊢
  intro m
  rw [coeff_weightedHomogeneousComponent]
  split_ifs
  · exact hx m
  · rw [norm_zero]; exact zero_le_one
end Formalism.InvariantFactorPaths.PW
