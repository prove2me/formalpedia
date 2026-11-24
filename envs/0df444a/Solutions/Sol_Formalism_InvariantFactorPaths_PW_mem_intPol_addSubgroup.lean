-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.mem_intPol_addSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:42.247623+00:00
-- url     : https://prove2.me/submissions/9c668a0e-4dc3-4ba2-a357-aa27f57b51bb

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatData
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_intPol_iff_norm


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
theorem _root_.solution {σ : Type} (x : MvPolynomial σ ℚ_[p]) :
    x ∈ (IntPol p σ).toAddSubgroup ↔ ∀ m, ‖x.coeff m‖ ≤ 1 := by
  rw [Submodule.mem_toAddSubgroup, intPol_iff_norm]
end Formalism.InvariantFactorPaths.PW
