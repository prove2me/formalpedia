-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_precontact_truegrid_caplinear_dividend_FV_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T21:00:42.626371+00:00
-- url     : https://prove2.me/submissions/7c19a8b9-1d48-4cf6-b400-deb42da32a60

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_caplinear_allcell_discounted_cash_loss_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hDstrategy : IsDividendStrategy 𝓕 D)
    (n m : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω)
    (u : ℕ → ℝ≥0)
    (hu : ∀ i, u i = min
      ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))) (ρ ω)) :
    let good : Finset ℕ :=
      (Finset.range (m + 1)).filter (fun i =>
        u (i + 1) = 0 ∨
          (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (∑ i ∈ good,
      Real.exp (-(q * (u (i + 1) : ℝ))) *
        ((rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) -
          (V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
           V (x + X.X (u (i + 1)) ω -
              rightLimit D (u (i + 1)) ω)))) ≤ 0 := by 
  classical
  intro good
  let pre : ℕ → ℝ := fun i =>
    x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
  let post : ℕ → ℝ := fun i =>
    x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω
  let weight : ℕ → ℝ := fun i =>
    Real.exp (-(q * (u (i + 1) : ℝ)))
  have hgrid (i : ℕ) : u i ≤ u (i + 1) := by
    rw [hu i, hu (i + 1)]
    have hi : (i : ℝ≥0) ≤ ((i + 1 : ℕ) : ℝ≥0) := by
      exact_mod_cast Nat.le_succ i
    exact min_le_min_right _ (mul_le_mul_of_nonneg_right hi (by positivity))
  have hactive (i : ℕ) (hi : i ∈ good) :
      u (i + 1) = 0 ∨
      (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω := by
    exact (Finset.mem_filter.mp hi).2
  have hpos (i : ℕ) (hi : i ∈ good) : 0 ≤ post i := by
    exact avram_p4_e_localise_preruin_postpayment_nonnegative
      X x C D hD ω (u (i + 1)) (hactive i hi)
  have hmono := avram_wave3_03_dividendStrategy_rightLimit_monotone
    D hDstrategy ω
  have hbound :=
    avram_pj_workerC_caplinear_allcell_discounted_cash_loss_nonpos
      good C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
      pre post weight
      (by intro i hi; exact hpos i hi)
      (by
        intro i hi
        dsimp [pre, post]
        linarith [hmono (hgrid i)])
      (by intro i hi; exact le_of_lt (Real.exp_pos _))
  have heq : (∑ i ∈ good,
      Real.exp (-(q * (u (i + 1) : ℝ))) *
        ((rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) -
          (V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
           V (x + X.X (u (i + 1)) ω -
              rightLimit D (u (i + 1)) ω)))) =
      ∑ i ∈ good,
        weight i * ((pre i - post i) - (V (pre i) - V (post i))) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [pre, post, weight]
    ring
  rw [heq]
  exact hbound
