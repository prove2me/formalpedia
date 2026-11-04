-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_anycap_finite_mesh_full_stieltjes_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:45:42.40341+00:00
-- url     : https://prove2.me/submissions/4ae6ea77-97a5-41d3-8161-d4fa8eb2c3b0

import Mathlib.Analysis.Calculus.ContDiff.Defs
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

/-- Every finite source-frozen payment mesh has nonpositive cumulative Stieltjes correction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
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
    (∑ i ∈ s, ((dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))).toReal +
      V (x + X.X (b i) ω - rightLimit D (b i) ω) -
      V (x + X.X (b i) ω - rightLimit D (a i) ω))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  exact avram_p4_d_dividend_original_anycap_true_payment_full_stieltjes_cell_budget
    X x C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite D hD ω
    (a i) (b i) (hab i hi) (hPay i hi)
