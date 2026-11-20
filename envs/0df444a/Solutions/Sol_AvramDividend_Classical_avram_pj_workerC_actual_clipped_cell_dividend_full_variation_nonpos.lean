-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_actual_clipped_cell_dividend_full_variation_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:44:20.47202+00:00
-- url     : https://prove2.me/submissions/bd9b14b9-752b-4d2d-a14e-24bd602653e0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_discounted_physical_dividend_cell_gradient_losses_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ)
    (n m : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω)
    (u : ℕ → ℝ≥0)
    (hu : ∀ i, u i = min
      ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))) (ρ ω))
    (hDmono : ∀ i ∈ Finset.range (m + 1),
      rightLimit D (u i) ω ≤ rightLimit D (u (i + 1)) ω)
    (hpost : ∀ i ∈ Finset.range (m + 1),
      0 ≤ x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)
    (hcap : ∀ i ∈ Finset.range (m + 1),
      ENNReal.ofReal (x + X.X (u (i + 1)) ω -
        rightLimit D (u i) ω) ≤ C) :
    (∑ i ∈ Finset.range (m + 1),
      Real.exp (-(q * (u (i + 1) : ℝ))) *
        ((rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) -
          (w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
           w (x + X.X (u (i + 1)) ω -
              rightLimit D (u (i + 1)) ω)))) ≤ 0 := by 
  classical
  let pre : ℕ → ℝ := fun i =>
    x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
  let post : ℕ → ℝ := fun i =>
    x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω
  let weight : ℕ → ℝ := fun i =>
    Real.exp (-(q * (u (i + 1) : ℝ)))
  have hneg :=
    avram_pj_workerC_discounted_physical_dividend_cell_gradient_losses_nonpos
      (Finset.range (m + 1)) C w hw_cont hw_smooth hw_grad
      pre post weight
      (by intro i hi; exact hpost i hi)
      (by
        intro i hi
        dsimp [pre, post]
        linarith [hDmono i hi])
      (by intro i hi; exact hcap i hi)
      (by intro i hi; exact le_of_lt (Real.exp_pos _))
  have heq : (∑ i ∈ Finset.range (m + 1),
      Real.exp (-(q * (u (i + 1) : ℝ))) *
        ((rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) -
          (w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
           w (x + X.X (u (i + 1)) ω -
              rightLimit D (u (i + 1)) ω)))) =
      ∑ i ∈ Finset.range (m + 1),
        weight i * ((pre i - post i) - (w (pre i) - w (post i))) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [pre, post, weight]
    ring
  rw [heq]
  exact hneg
