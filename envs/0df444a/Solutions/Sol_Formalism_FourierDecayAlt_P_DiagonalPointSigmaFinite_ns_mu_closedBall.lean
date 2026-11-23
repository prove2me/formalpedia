-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_mu_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:26.881193+00:00
-- url     : https://prove2.me/submissions/27b6dd7e-f310-4cfc-bfa5-e7c59e7a3830

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
theorem _root_.solution (β : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    mu β (Metric.closedBall 0 R) = ENNReal.ofReal (‖β‖ / 2 * R ^ 2) := by
  have hpi : (NNReal.pi : ENNReal) = ENNReal.ofReal Real.pi := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  unfold mu
  rw [Measure.smul_apply, Complex.volume_closedBall, ENNReal.smul_def, smul_eq_mul, hpi,
    ← ENNReal.ofReal_pow hR, ← ENNReal.ofReal_mul (by positivity)]
  change ENNReal.ofReal (‖β‖ / (2 * Real.pi)) * _ = _
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
