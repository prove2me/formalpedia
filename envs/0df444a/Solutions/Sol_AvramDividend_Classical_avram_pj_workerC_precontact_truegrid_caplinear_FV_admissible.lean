-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_precontact_truegrid_caplinear_FV_admissible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T21:07:24.315961+00:00
-- url     : https://prove2.me/submissions/a0e912be-629e-44a7-b451-1866bbd26efe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_caplinear_allcell_discounted_cash_loss_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_precontact_truegrid_caplinear_dividend_FV_nonpos
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
  exact avram_pj_workerC_precontact_truegrid_caplinear_dividend_FV_nonpos
    X x q C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
    D hD hD.1.1 n m ρ ω u hu
