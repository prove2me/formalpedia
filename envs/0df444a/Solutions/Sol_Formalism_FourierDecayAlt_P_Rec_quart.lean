-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Rec.quart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:34.41886+00:00
-- url     : https://prove2.me/submissions/02a4bf5a-ab4a-4539-811a-e7f5fe6b1866

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SharpRecursion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Rec
open Finset Real
namespace Formalism.FourierDecayAlt.P.Rec
theorem _root_.solution (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : (1 + 2 * x) ^ 4 ≤ 1 + 80 * x := by
  have h2 : x ^ 2 ≤ x := by nlinarith
  have h3 : x ^ 3 ≤ x := by nlinarith
  have h4 : x ^ 4 ≤ x := by nlinarith
  nlinarith
end Formalism.FourierDecayAlt.P.Rec
