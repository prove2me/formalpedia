-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.rpow_decay_arith
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:44.852359+00:00
-- url     : https://prove2.me/submissions/61772742-6f00-4920-83e8-64993e09c027

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
theorem _root_.solution {τ ε : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (q N p : ℕ)
    (h : ε * (N : ℝ) + (p : ℝ) ≤ (q : ℝ)) : τ ^ q * (τ ^ (-ε)) ^ N ≤ τ ^ p := by
  rw [← Real.rpow_mul_natCast hτ.le, ← Real.rpow_natCast τ q, ← Real.rpow_natCast τ p, ← Real.rpow_add hτ]
  exact Real.rpow_le_rpow_of_exponent_ge hτ hτ1 (by linarith)
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
