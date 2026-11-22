-- Prove2me | solution 1 for Formalism.CountingSumsFrames.pII0_one_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:45:57.764441+00:00
-- url     : https://prove2.me/submissions/3404ba84-4f20-40c3-8e3a-decac589ef8f

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SecondParameterSizeBoundsHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CountingSumsFrames
open Real
namespace Formalism.CountingSumsFrames
theorem _root_.solution {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  nlinarith
end Formalism.CountingSumsFrames
