-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G3.aux
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:11.134809+00:00
-- url     : https://prove2.me/submissions/0b22dea4-8a74-4f43-8c7f-88c69fc7b3fe

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G3
namespace Formalism.FourierDecayAlt.P.G3
theorem _root_.solution (a R : ℝ) (ha : 0 ≤ a) (h : a ≤ R) : a ≤ max 1 R * min 1 a := by
  rcases le_total a 1 with h1 | h1
  · rw [min_eq_right h1]
    nlinarith [le_max_left 1 R]
  · rw [min_eq_left h1]
    simpa using h.trans (le_max_right 1 R)
end Formalism.FourierDecayAlt.P.G3
