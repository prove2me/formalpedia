-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_sum_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:23.947807+00:00
-- url     : https://prove2.me/submissions/66528ae9-b350-47cd-9f53-be01ce08bd15

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp
import Theorems.Thm_Formalism_CountingSumsFrames_segment_ratio_le
import Theorems.Thm_Formalism_CountingSumsFrames_segment_ratio_le_prime

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
theorem _root_.solution {k Y L a b' p P S Y' : ℝ} (hk : 0 < k) (hY : 0 < Y) (hL : 0 < L) (ha : 0 < a) (hb : 0 < b')
    (hp : k^2*Y^2 ≤ p) (h2 : k*Y^2*L ≤ a/b') (hP : 0 < P) (hS0 : 0 ≤ S)
    (hS : S ≤ (4*a/p^2+2*b')/P) (hY' : a/(2*k*Y*P) ≤ Y') :
    S / Y' ≤ 8/(k^3*Y^3) + 4/(Y*L) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hw : 0 < a/(2*k*Y*P) := by positivity
  calc S / Y' ≤ S / (a/(2*k*Y*P)) := div_le_div_of_nonneg_left hS0 hw hY'
    _ ≤ ((4*a/p^2+2*b')/P) / (a/(2*k*Y*P)) := div_le_div_of_nonneg_right hS hw.le
    _ = 8 * (k*Y/p^2) + 4*(k*Y*b'/a) := by field_simp; ring
    _ ≤ 8*(1/(k^3*Y^3)) + 4*(1/(Y*L)) := by
        have h1 := segment_ratio_le_prime hk hY hp
        have h3 := segment_ratio_le hk hY hL ha hb h2
        linarith
    _ = _ := by ring
end Formalism.CountingSumsFrames
