-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_actual_clipped_cell_caplinear_full_dividend_from_strategy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T21:00:50.683492+00:00
-- url     : https://prove2.me/submissions/3113e664-edf7-4e2f-a8c1-40834b2b4635

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_caplinear_allcell_discounted_cash_loss_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_clipped_cell_caplinear_full_dividend_nonpos_v2
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n m : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω)
    (u : ℕ → ℝ≥0)
    (hu : ∀ i, u i = min
      ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))) (ρ ω))
    (hpost : ∀ i ∈ Finset.range (m + 1),
      0 ≤ x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) :
    (∑ i ∈ Finset.range (m + 1),
      Real.exp (-(q * (u (i + 1) : ℝ))) *
        ((rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) -
          (V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
           V (x + X.X (u (i + 1)) ω -
              rightLimit D (u (i + 1)) ω)))) ≤ 0 := by 
  classical
  have hgrid (i : ℕ) : u i ≤ u (i + 1) := by
    rw [hu i, hu (i + 1)]
    have hi : (i : ℝ≥0) ≤ ((i + 1 : ℕ) : ℝ≥0) := by
      exact_mod_cast Nat.le_succ i
    exact min_le_min_right _ (mul_le_mul_of_nonneg_right hi (by positivity))
  have hDmono : ∀ i ∈ Finset.range (m + 1),
      rightLimit D (u i) ω ≤ rightLimit D (u (i + 1)) ω := by
    intro i hi
    exact (avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω)
      (hgrid i)
  exact avram_pj_workerC_actual_clipped_cell_caplinear_full_dividend_nonpos_v2
    X x q C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
    D n m ρ ω u hu hDmono hpost
