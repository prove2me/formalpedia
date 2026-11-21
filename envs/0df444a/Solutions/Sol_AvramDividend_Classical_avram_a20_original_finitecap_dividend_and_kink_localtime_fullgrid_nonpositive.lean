-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_finitecap_dividend_and_kink_localtime_fullgrid_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:44:06.298331+00:00
-- url     : https://prove2.me/submissions/f3a506a6-d4c1-49c9-8121-0d6fb2be332b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a19_original_finitecap_HJB_gradient_grid_payment_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_finitecap_grid_discounted_kink_localtime_sum_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original finite-cap right-dividend and Gaussian cap-kink local-time grid channels are jointly nonpositive. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (S : Finset ℕ) (j : ℕ → ℕ)
    (Y D E L K : ℕ → ℝ)
    (hYlo : ∀ i ∈ S, 0 ≤ Y i)
    (hYhi : ∀ i ∈ S, Y i ≤ C.toReal)
    (hD : ∀ i ∈ S, 0 ≤ D i)
    (hE : ∀ i ∈ S, 0 ≤ E i)
    (hL : ∀ i ∈ S, 0 ≤ L i)
    (hK : ∀ i ∈ S, 0 ≤ K i)
    (hw_cont : ContinuousOn w (Ici 0))
    (hDiff : ∀ i ∈ S, DifferentiableOn ℝ w (Ioo (Y i) C.toReal))
    (hGradBand : ∀ i ∈ S, ∀ t ∈ Ioo (Y i) C.toReal,
      1 ≤ deriv w t) :
    (∑ i ∈ S, E i * (D i + w (Y i) -
        (if Y i + D i ≤ C.toReal then w (Y i + D i)
         else w C.toReal + (Y i + D i - C.toReal)))) +
    (∑ i ∈ S, K i *
      (((1 - deriv w
        (C.toReal * ((((j i + 1 : ℕ) : ℝ) / ((j i + 2 : ℕ) : ℝ))))) / 2) * L i))
    ≤ 0  := by
  have hPay :=
    avram_a19_original_finitecap_HJB_gradient_grid_payment_nonpositive
      S w C.toReal Y D E hYlo hYhi hD hE
      hw_cont hDiff hGradBand
  have hKink :=
    avram_jump6_B_original_finitecap_grid_discounted_kink_localtime_sum_nonpos
      w C hC hFiniteCap hw_smooth hw_grad
      S j L K hL hK
  exact add_nonpos hPay hKink
