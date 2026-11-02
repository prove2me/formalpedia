-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_original_finite_right_payment_signed_caplinear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:49:08.563308+00:00
-- url     : https://prove2.me/submissions/37a7cb5e-711c-4104-8f9a-ca70a7719d75

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (q : ℝ) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y)
    (hV : ∀ y : ℝ, V y = if y ≤ c then w y else w c + (y - c))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (t : ℕ → ℝ≥0) (n : ℕ)
    (hPre : ∀ k : ℕ, k < n →
      t k = 0 ∨ (t k : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ k ∈ Finset.range n,
      Real.exp (-(q * (t k : ℝ))) *
        ((rightLimit D (t k) ω - D (t k) ω) +
          V (riskProcess X x D (t k) ω -
            (rightLimit D (t k) ω - D (t k) ω)) -
          V (riskProcess X x D (t k) ω))) ≤ 0 := by
  have hAdmissible : IsAdmissible X x D := hD.1
  have hStrategy : IsDividendStrategy 𝓕 D := hAdmissible.1
  apply Finset.sum_nonpos
  intro k hk
  let U : ℝ := riskProcess X x D (t k) ω
  let δ : ℝ := rightLimit D (t k) ω - D (t k) ω
  have hpay : 0 ≤ δ := sub_nonneg.mpr
    (dividendStrategy_le_rightLimit D hStrategy ω (t k))
  have hpost : 0 ≤ U - δ := by
    have hs := hAdmissible.2 ω (t k) (hPre k (Finset.mem_range.mp hk))
    change δ ≤ U at hs
    linarith only [hs]
  have horder : U - δ ≤ U := by linarith only [hpay]
  have hsec := avram_wave4_04_cap_linear_extension_full_secant
    c hc w hw_cont hw_smooth hw_grad (U - δ) U hpost horder
  rw [← hV U, ← hV (U - δ)] at hsec
  have hsign : δ + V (U - δ) - V U ≤ 0 := by
    linarith only [hsec]
  change Real.exp (-(q * (t k : ℝ))) *
    (δ + V (U - δ) - V U) ≤ 0
  exact mul_nonpos_of_nonneg_of_nonpos
    (le_of_lt (Real.exp_pos _)) hsign
