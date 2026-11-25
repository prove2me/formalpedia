-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.circleMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:13:53.237797+00:00
-- url     : https://prove2.me/submissions/03265b13-7145-4be2-9453-e52ded69489b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BasePointMemHalfPlane
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaAtBasePointZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_exp_base_point_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex MeasureTheory intervalIntegral
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {TT : ℝ} {α : ℂ → ℂ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (hTT : 0 ≤ TT) (θ : ℝ) : circleMap 0 (TT + 1) θ = Complex.exp (x0 TT + (θ : ℂ) * I) := by
  simp [circleMap, Complex.exp_add, exp_base_point_eq hTT]
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
