-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.hasFDerivAt_br_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:16:23.724163+00:00
-- url     : https://prove2.me/submissions/8aae6217-5fb3-4db3-bd0e-51129274ddbe

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NeZeroOfAn
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtBrReal
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_hasDerivAt_br


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {TT : ℝ} {α : ℂ → ℂ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s) :
    HasFDerivAt (br s) ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹) ζ := by
  have h : HasFDerivAt (br s)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) ζ⁻¹).restrictScalars ℝ) ζ :=
    (hasDerivAt_br s hs).hasFDerivAt.restrictScalars ℝ
  convert h using 1
  refine ContinuousLinearMap.ext fun v => ?_
  simp [mul_comm]
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
