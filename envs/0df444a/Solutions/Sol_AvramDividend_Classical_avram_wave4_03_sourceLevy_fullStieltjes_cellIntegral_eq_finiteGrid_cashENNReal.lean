-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_fullStieltjes_cellIntegral_eq_finiteGrid_cashENNReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:36:30.926566+00:00
-- url     : https://prove2.me/submissions/8deaaefe-0efd-446e-8b66-7a4af06544b6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_fullStieltjes_cellIndicator_lintegral_eq_sum
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Exact source-X finite Stieltjes indicator integral equals its original
postpayment exponential cash, retaining continuous and right-atomic mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) (ω : Ω) :
    (∫⁻ s : ℝ, ∑ i ∈ Finset.range n,
      if s ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) then
        ENNReal.ofReal (θ *
          Real.exp (θ * X.X (u (i + 1)) ω -
            (u (i + 1) : ℝ) * X.ψ θ) *
          Real.exp (-(θ * rightLimit D (u (i + 1)) ω)))
      else 0 ∂dividendMeasure D ω) =
    ENNReal.ofReal (θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) := by
  have hd (i : ℕ) :
      0 ≤ rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω := by
    exact sub_nonneg.mpr (avram_wave3_03_dividendStrategy_rightLimit_monotone
      D hD ω (hu (Nat.le_succ i)))
  have hw (i : ℕ) :
      0 ≤ θ *
        Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
        Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) := by
    positivity
  calc
    _ = ∑ i ∈ Finset.range n,
      ENNReal.ofReal (θ *
        Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
        Real.exp (-(θ * rightLimit D (u (i + 1)) ω))) *
      dividendMeasure D ω (Ioc (u i : ℝ) (u (i + 1) : ℝ)) :=
        avram_wave4_03_sourceLevy_fullStieltjes_cellIndicator_lintegral_eq_sum
          X D θ u n ω
    _ = ∑ i ∈ Finset.range n,
      ENNReal.ofReal (θ *
        Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
        Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [dividendMeasure_Ioc_rightLimit D hD ω (u i) (u (i + 1))]
      exact (ENNReal.ofReal_mul (hw i)).symm
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n,
      θ *
        Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
        Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro i hi
      exact mul_nonneg (hw i) (hd i)
    _ = _ := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
