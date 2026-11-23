-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_ratio_le_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:40.161799+00:00
-- url     : https://prove2.me/submissions/c8b598eb-0ab1-4769-a13e-cf490ea07a7c

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
theorem _root_.solution {k Y p : ℝ} (hk : 0 < k) (hY : 0 < Y) (hp : k^2*Y^2 ≤ p) :
    k*Y/p^2 ≤ 1/(k^3*Y^3) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc k*Y*(k^3*Y^3) = (k^2*Y^2)^2 := by ring
    _ ≤ p^2 := by gcongr
    _ = 1*p^2 := by ring
end Formalism.CountingSumsFrames
