-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G8.norm_gK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:37.331366+00:00
-- url     : https://prove2.me/submissions/9829992b-c512-4e00-837b-5af51e46683e

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G8
namespace Formalism.FourierDecayAlt.P.G8
theorem _root_.solution (δ p q : ℝ) (z : ℝ × ℝ) :
    ‖gK δ p q z‖ = Real.exp (-δ * z.1 ^ 2) * Real.exp (-δ * z.2 ^ 2) := by
  rw [gK, Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp [pow_two]
  ring
end Formalism.FourierDecayAlt.P.G8
