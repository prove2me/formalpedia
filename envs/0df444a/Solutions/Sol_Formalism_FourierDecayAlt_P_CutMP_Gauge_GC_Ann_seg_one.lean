-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.seg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:18:53.932207+00:00
-- url     : https://prove2.me/submissions/16d613ae-fcfa-47ad-bec3-53ca357fb5d9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtTMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtPrim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology MeasureTheory intervalIntegral Metric
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {ω : ℂ → ℂ →L[ℝ] ℝ} {S : Set ℂ} {w₀ : ℂ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (w₀ x : ℂ) : seg w₀ x 1 = x := by
  simp [seg]
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
