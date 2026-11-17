-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB32_original_cap_quadratic_preruin_reward_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T19:03:24.455978+00:00
-- url     : https://prove2.me/submissions/728e5b12-64a7-4d0b-a39d-1be38fd3f601

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_reserve_cap_bound_all_capital
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) <
        ruinTime X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω →
      0 ≤ (fun z : ℝ => if z < 0 then 0 else 2 * z - 4 * z ^ 2)
        (riskProcess X (1 / 8 : ℝ)
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω) := by 
  intro ω t ht hruin
  let x : ℝ := 1 / 8
  let D : ℝ≥0 → Ω → ℝ := barrierStrategy X x x
  let y : ℝ := riskProcess X x D t ω
  have hy0 : 0 ≤ y :=
    riskProcess_nonnegative_strictly_before_ruin X x D ω t hruin
  have hCap := barrierStrategy_reserve_cap_bound_all_capital X x x
    (by norm_num [x]) (by norm_num [x]) ω t ht
  have hyC : y ≤ x :=
    (ENNReal.ofReal_le_ofReal_iff (by norm_num [x])).mp hCap
  have hp : 0 ≤ y * (1 / 2 - y) := by
    exact mul_nonneg hy0 (by dsimp [x] at hyC; linarith)
  change 0 ≤ if y < 0 then 0 else 2 * y - 4 * y ^ 2
  simp only [not_lt.mpr hy0, ↓reduceIte]
  nlinarith
