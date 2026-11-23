-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_muPi_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:56.86392+00:00
-- url     : https://prove2.me/submissions/896330bb-620b-41d5-8a13-8755894bb4f1

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_mu_closedBall

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
theorem _root_.solution (β : ℂ) (ι : Type) [Fintype ι] (R : ℝ) (hR : 0 ≤ R) :
    muPi β ι (Metric.closedBall 0 R) = ENNReal.ofReal ((‖β‖ / 2 * R ^ 2) ^ Fintype.card ι) := by
  unfold muPi
  rw [closedBall_pi _ hR, Measure.pi_pi]
  simp only [Pi.zero_apply, ns_mu_closedBall β R hR, Finset.prod_const, Finset.card_univ]
  rw [ENNReal.ofReal_pow (by positivity)]
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
