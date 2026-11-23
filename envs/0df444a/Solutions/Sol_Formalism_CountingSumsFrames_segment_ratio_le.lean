-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:57.804457+00:00
-- url     : https://prove2.me/submissions/7458f026-e736-4a64-b706-100717d772f5

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution {k Y L a b' : ℝ} (_hk : 0 < k) (hY : 0 < Y) (hL : 0 < L) (ha : 0 < a) (hb : 0 < b')
    (h2 : k*Y^2*L ≤ a/b') : k * Y * b' / a ≤ 1 / (Y * L) := by
  rw [div_le_div_iff₀ ha (by positivity)]
  have := (le_div_iff₀ hb).1 h2
  calc k*Y*b'*(Y*L) = k*Y^2*L*b' := by ring
    _ ≤ a := this
    _ = 1*a := by ring
end Formalism.CountingSumsFrames
