-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_original_preruin_weighted_signed_stieltjes_step_partition_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:40:24.804404+00:00
-- url     : https://prove2.me/submissions/aabb6917-6b58-4eb9-9fae-a45bf4106cb5

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_interval_full_dividend_measure_signed_domination

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The genuine Stieltjes dividend measure is dominated by source-frozen cap-linear drops against every nonnegative step weight. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z = if z ≤ c then w z else w c + (z - c))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (r : ℕ → ℝ) (hr : ∀ i : ℕ, i < n → 0 ≤ r i) :
    ∑ i ∈ Finset.range n,
      (r i * (
        (dividendMeasure D ω (Ioc (u i : ℝ) (u (i + 1) : ℝ))).toReal +
        V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
        V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  have hii : i < n := Finset.mem_range.mp hi
  have hCell := avram_wave5_04b_original_preruin_interval_full_dividend_measure_signed_domination
    X x c hc w V hw_cont hw_smooth hw_grad hV D hD ω
    (u i) (u (i + 1)) (hGrid i hii) (hPre i hii)
  exact mul_nonpos_of_nonneg_of_nonpos (hr i hii) hCell
