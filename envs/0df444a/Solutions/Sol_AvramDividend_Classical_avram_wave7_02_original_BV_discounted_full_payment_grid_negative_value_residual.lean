-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_discounted_full_payment_grid_negative_value_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:33:42.81098+00:00
-- url     : https://prove2.me/submissions/9f9f6000-4bde-4853-9335-568ddd4028f5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_compact_stopped_full_right_dividend_C1_pathwise_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

/-- Full actual discounted right-dividend grid with exact negative value discount residual, no global or sampled sign assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (a b L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hbC : ENNReal.ofReal b ≤ C) (hL1 : 1 ≤ L)
    (hLip : ∀ y ∈ Icc a b, ∀ z ∈ Icc a b,
      |w y - w z| ≤ L * |y - z|)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u →
      (∀ n, x + X.X (u n) ω - rightLimit D (u n) ω ∈ Icc a b) →
      ∀ n,
        (∑ i ∈ Finset.range n,
          Real.exp (-(q * (u (i + 1) : ℝ))) *
            (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) +
        Real.exp (-(q * (u n : ℝ))) *
          w (x + X.X (u n) ω - rightLimit D (u n) ω) ≤
        Real.exp (-(q * (u 0 : ℝ))) *
          w (x + X.X (u 0) ω - rightLimit D (u 0) ω) +
        (∑ i ∈ Finset.range n,
          Real.exp (-(q * (u (i + 1) : ℝ))) *
            (L * (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) +
        (∑ i ∈ Finset.range n,
          (Real.exp (-(q * (u i : ℝ))) -
            Real.exp (-(q * (u (i + 1) : ℝ)))) *
            max 0 (-(w (x + X.X (u i) ω - rightLimit D (u i) ω)))) := by
  filter_upwards
    [avram_wave7_02_original_BV_compact_stopped_full_right_dividend_C1_pathwise_budget
      X hX hBV x D hD C hC w hw_cont hw_smooth hw_grad
      a b L ha hab hbC hL1 hLip] with ω hPath
  intro u hu hBand n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hnt : u n ≤ u (n + 1) := hu (Nat.le_succ n)
      have hPair := hPath (u n) (u (n + 1))
        hnt (hBand n) (hBand (n + 1))
      have hCoerce : (u n : ℝ) ≤ (u (n + 1) : ℝ) := by
        exact_mod_cast hnt
      have hTimes : q * (u n : ℝ) ≤ q * (u (n + 1) : ℝ) :=
        mul_le_mul_of_nonneg_left hCoerce hq
      have hExp : Real.exp (-(q * (u (n + 1) : ℝ))) ≤
          Real.exp (-(q * (u n : ℝ))) := by
        exact Real.exp_le_exp.mpr (neg_le_neg hTimes)
      have hScaled := mul_le_mul_of_nonneg_left hPair
        (le_of_lt (Real.exp_pos (-(q * (u (n + 1) : ℝ)))))
      have hPart : 0 ≤
          w (x + X.X (u n) ω - rightLimit D (u n) ω) +
          max 0 (-(w (x + X.X (u n) ω - rightLimit D (u n) ω))) := by
        have hMax : -(w (x + X.X (u n) ω - rightLimit D (u n) ω)) ≤
            max 0 (-(w (x + X.X (u n) ω - rightLimit D (u n) ω))) :=
          le_max_right _ _
        linarith only [hMax]
      have hOld :
          Real.exp (-(q * (u (n + 1) : ℝ))) *
            w (x + X.X (u n) ω - rightLimit D (u n) ω) ≤
          Real.exp (-(q * (u n : ℝ))) *
            w (x + X.X (u n) ω - rightLimit D (u n) ω) +
          (Real.exp (-(q * (u n : ℝ))) -
            Real.exp (-(q * (u (n + 1) : ℝ)))) *
            max 0 (-(w (x + X.X (u n) ω - rightLimit D (u n) ω))) := by
        have hProd := mul_nonneg (sub_nonneg.mpr hExp) hPart
        nlinarith only [hProd]
      have hStep :
          Real.exp (-(q * (u (n + 1) : ℝ))) *
            (rightLimit D (u (n + 1)) ω - rightLimit D (u n) ω) +
          Real.exp (-(q * (u (n + 1) : ℝ))) *
            w (x + X.X (u (n + 1)) ω - rightLimit D (u (n + 1)) ω) ≤
          Real.exp (-(q * (u n : ℝ))) *
            w (x + X.X (u n) ω - rightLimit D (u n) ω) +
          Real.exp (-(q * (u (n + 1) : ℝ))) *
            (L * (((u (n + 1) : ℝ) - (u n : ℝ)) * X.drift)) +
          (Real.exp (-(q * (u n : ℝ))) -
            Real.exp (-(q * (u (n + 1) : ℝ)))) *
            max 0 (-(w (x + X.X (u n) ω - rightLimit D (u n) ω))) := by
        nlinarith only [hScaled, hOld]
      simp only [Finset.sum_range_succ]
      linarith only [ih, hStep]
