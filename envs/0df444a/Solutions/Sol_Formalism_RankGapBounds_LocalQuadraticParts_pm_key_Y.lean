-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.pm_key_Y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:35:57.22316+00:00
-- url     : https://prove2.me/submissions/ef288ba9-4b11-4773-8972-7920e0bd6489

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.RankGapBounds.LocalQuadraticParts
open Finset
private theorem log_le_log_of_pos_of_le {a b : ℝ} (ha : 0 < a) (h : a ≤ b) : Real.log a ≤ Real.log b := by
  exact Real.log_le_log ha h
private theorem div_le_div_of_mul_le_mul_of_pos' {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d)
    (h : a * d ≤ c * b) : a / b ≤ c / d := by
  first
  | exact (div_le_div_iff_of_pos hb hd).mpr h
  | exact (div_le_div_iff hb hd).mpr h
  | exact (div_le_div_iff₀ hb hd).mpr h
end Formalism.RankGapBounds.LocalQuadraticParts
end

set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.LocalQuadraticParts
open Finset
namespace Formalism.RankGapBounds.LocalQuadraticParts
theorem _root_.solution (m x y Y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (h1 : x * y / 2 ≤ m) (hmY : m ≤ Y)
    (hm1 : 1 ≤ m) : Real.log m / m ≤ Real.log Y * (2 / y) * (1 / x) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hm0 : 0 < m := by linarith
  have hlm : 0 ≤ Real.log m := Real.log_nonneg hm1
  have hlmY : Real.log m ≤ Real.log Y := log_le_log_of_pos_of_le hm0 hmY
  have hlY : 0 ≤ Real.log Y := le_trans hlm hlmY
  rw [show Real.log Y * (2 / y) * (1 / x) = 2 * Real.log Y / (x * y) by ring]
  apply div_le_div_of_mul_le_mul_of_pos' hm0 (mul_pos hx0 hy0)
  nlinarith [mul_le_mul_of_nonneg_right hlmY (mul_pos hx0 hy0).le,
    mul_le_mul_of_nonneg_left h1 hlY]
end Formalism.RankGapBounds.LocalQuadraticParts
