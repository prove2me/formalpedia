-- Prove2me | solution 1 for AvramDividend.Classical.compensated_primitive_quadratic_large_mark_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T21:34:29.417906+00:00
-- url     : https://prove2.me/submissions/e96bba0f-e47c-440d-ab78-3237c3abc01b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_primitive_bounds
open MeasureTheory Set AvramDividend.Classical

theorem solution (θ y : ℝ) (hθ : 0 ≤ θ) (hy : y < 0) :
    0 ≤ (∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ∧
    (∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ≤
      θ / 2 * min 1 (y ^ 2) +
        |(Iic (-1 : ℝ)).indicator (fun z : ℝ => z) y| := by
  have hz : 0 ≤ -y := by linarith
  obtain ⟨hp, hq, hl⟩ :=
    levy_compensated_exponential_primitive_bounds θ (-y) hθ hz
  refine ⟨hp, ?_⟩
  by_cases hbig : y ≤ -1
  · have hmem : y ∈ Iic (-1 : ℝ) := hbig
    have hval :
        (Iic (-1 : ℝ)).indicator (fun z : ℝ => z) y = y :=
      Set.indicator_of_mem hmem (fun z : ℝ => z)
    have hn : 0 ≤ θ / 2 * min 1 (y ^ 2) := by positivity
    rw [hval, abs_of_neg hy]
    linarith
  · have hnot : y ∉ Iic (-1 : ℝ) := hbig
    have hval :
        (Iic (-1 : ℝ)).indicator (fun z : ℝ => z) y = 0 :=
      Set.indicator_of_notMem hnot (fun z : ℝ => z)
    have hlow : -1 < y := lt_of_not_ge hbig
    have hs : y ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg
        (show 0 ≤ y + 1 by linarith)
        (show 0 ≤ 1 - y by linarith)]
    have hm : min 1 (y ^ 2) = y ^ 2 := min_eq_right hs
    rw [hval, abs_zero, add_zero, hm]
    nlinarith [hq]
