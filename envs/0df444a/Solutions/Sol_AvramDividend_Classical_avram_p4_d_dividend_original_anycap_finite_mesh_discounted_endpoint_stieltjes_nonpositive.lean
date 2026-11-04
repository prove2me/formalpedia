-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_anycap_finite_mesh_discounted_endpoint_stieltjes_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:28:34.225204+00:00
-- url     : https://prove2.me/submissions/4f37278b-4e2e-4b8c-bd6c-8472a6242549

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_anycap_true_payment_full_stieltjes_cell_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Endpoint-discounted original full Stieltjes cells have a nonpositive correction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (s : Finset ι) (a b : ι → ℝ≥0)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hPay : ∀ i ∈ s, (b i : ℝ) ∈ paymentTimes (ruinTime X x D ω)) :
    (∑ i ∈ s, Real.exp (-(q * (b i : ℝ))) *
      ((dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))).toReal +
        V (x + X.X (b i) ω - rightLimit D (b i) ω) -
        V (x + X.X (b i) ω - rightLimit D (a i) ω))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _))
    (avram_p4_d_dividend_original_anycap_true_payment_full_stieltjes_cell_budget
      X x C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite D hD ω
      (a i) (b i) (hab i hi) (hPay i hi))
