-- Prove2me | solution 1 for Formalism.CountingSumsFrames.depth_real_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:19.932774+00:00
-- url     : https://prove2.me/submissions/980cbb07-d658-4f53-becd-22c30e771381

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution {T S M R Y lg κ fl : ℝ} (hY : 1 ≤ Y) (hR : 2 ≤ R) (hM : 1 ≤ M) (hT0 : 0 ≤ T)
    (hTS : T ≤ S) (hSM : S ≤ M) (hlg : 0 ≤ lg) (hκdef : κ = 3 * (S + 2) * R ^ 2 * lg)
    (hfl : fl ≤ Y * (T * (Y * κ + κ) + κ)) :
    fl + 3 * (S + 1) * lg + 2 * ((T + 1) * (R + 1) * lg) ≤ 45 * Y ^ 2 * M ^ 2 * (R + 1) ^ 2 * lg := by
  have hY0 : 0 < Y := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hκ0 : 0 ≤ κ := by rw [hκdef]; positivity
  have hκ : κ ≤ 9 * M * (R + 1) ^ 2 * lg := by
    rw [hκdef]
    have h1 : 3 * (S + 2) ≤ 9 * M := by linarith
    have h2 : R ^ 2 ≤ (R + 1) ^ 2 := by gcongr; linarith
    gcongr
  have hκY : κ ≤ Y * κ := le_mul_of_one_le_left hκ0 hY
  have hD1 : T * (Y * κ + κ) + κ ≤ 2 * (T + 1) * (Y * κ) := by
    have h1 : T * (Y * κ + κ) ≤ T * (2 * (Y * κ)) := by gcongr; linarith
    linarith
  have hYD : Y * (T * (Y * κ + κ) + κ) ≤ 36 * Y ^ 2 * M ^ 2 * (R + 1) ^ 2 * lg := by
    calc Y * (T * (Y * κ + κ) + κ) ≤ Y * (2 * (T + 1) * (Y * κ)) := by gcongr
      _ ≤ Y * (2 * (2 * M) * (Y * (9 * M * (R + 1) ^ 2 * lg))) := by gcongr; linarith
      _ = 36 * Y ^ 2 * M ^ 2 * (R + 1) ^ 2 * lg := by ring
  have h3 : 3 * (S + 1) * lg + 2 * ((T + 1) * (R + 1) * lg) ≤ κ := by
    rw [hκdef]
    have hc : 3 * (S + 1) + 2 * ((T + 1) * (R + 1)) ≤ 3 * (S + 2) * R ^ 2 := by
      have e1 : (T + 1) * (R + 1) ≤ (S + 1) * (R + 1) := by gcongr
      have e2 : 2 * R + 5 ≤ 3 * R ^ 2 := by nlinarith
      have e3 : (S + 1) * (2 * R + 5) ≤ (S + 1) * (3 * R ^ 2) := by gcongr
      have e4 : 0 ≤ R ^ 2 := by positivity
      linarith
    calc 3 * (S + 1) * lg + 2 * ((T + 1) * (R + 1) * lg)
        = (3 * (S + 1) + 2 * ((T + 1) * (R + 1))) * lg := by ring
      _ ≤ 3 * (S + 2) * R ^ 2 * lg := by gcongr
  have h4 : κ ≤ 9 * Y ^ 2 * M ^ 2 * (R + 1) ^ 2 * lg := by
    have hY2 : 1 ≤ Y ^ 2 := one_le_pow₀ hY
    calc κ ≤ 9 * M * (R + 1) ^ 2 * lg := hκ
      _ = 9 * 1 * (M * 1) * (R + 1) ^ 2 * lg := by ring
      _ ≤ 9 * Y ^ 2 * (M * M) * (R + 1) ^ 2 * lg := by gcongr
      _ = 9 * Y ^ 2 * M ^ 2 * (R + 1) ^ 2 * lg := by ring
  linarith
end Formalism.CountingSumsFrames
