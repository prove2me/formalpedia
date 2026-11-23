-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_vpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:27.610829+00:00
-- url     : https://prove2.me/submissions/f2c6232e-4c1f-439a-9b17-7423aeae4d2b

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
theorem _root_.solution {τ ε e : ℝ} (hτ : 0 ≤ τ) (n : ℕ) (hn : (n : ℝ) = e) :
    τ ^ (-(ε * e)) = (τ ^ (-ε)) ^ n := by
  rw [← Real.rpow_mul_natCast hτ, hn]
  congr 1; ring
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
