-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_original_diffuse_w_positive_atoms_initial_V_signed_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:58:50.818643+00:00
-- url     : https://prove2.me/submissions/ff5d783c-afc6-4f6b-a1e3-19467bbf7627

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_original_positive_countable_w_right_payment_correction_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Actual original diffuse (including singular continuous) dividends and
positive jumps pay for themselves; the zero atom uses cap-linear V. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y
        else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (ν : Measure ℝ) [NullSingletonClass ν]
    (A : Set ℝ≥0) (hCount : A.Countable)
    (hA : ∀ t : A, 0 < (t : ℝ≥0) ∧
      ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω)
    (hlocAe : ∀ᵐ s ∂ν.restrict
        (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)),
      0 < riskProcess X x D s.toNNReal ω ∧
        ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C)
    (hIntegrable : IntegrableOn
      (fun s : ℝ => Real.exp (-q * s) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)))
      (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)) ν)
    (hSummable : Summable (fun t : A =>
      Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          w (riskProcess X x D (t : ℝ≥0) ω)))) :
    ((∫ s in paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ),
      Real.exp (-q * s) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂ν) +
    (∑' t : A, Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        w (riskProcess X x D (t : ℝ≥0) ω -
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
        w (riskProcess X x D (t : ℝ≥0) ω)))) +
    ((rightLimit D 0 ω - D 0 ω) +
      V (riskProcess X x D 0 ω -
        (rightLimit D 0 ω - D 0 ω)) -
      V (riskProcess X x D 0 ω)) ≤ 0 := by
  have hAe :
      ∀ᵐ s ∂ν.restrict
          (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)),
        Real.exp (-q * s) *
          (1 - deriv w (riskProcess X x D s.toNNReal ω)) ≤ 0 := by
    filter_upwards [hlocAe] with s hs
    have hg := hw_grad (riskProcess X x D s.toNNReal ω) hs.1 hs.2
    exact mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (Real.exp_pos _)) (by linarith)
  have hDiffuse :
      (∫ s in paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ),
        Real.exp (-q * s) *
          (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂ν) ≤ 0 := by
    change (∫ s : ℝ, Real.exp (-q * s) *
      (1 - deriv w (riskProcess X x D s.toNNReal ω))
      ∂ν.restrict
        (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ))) ≤ 0
    exact integral_nonpos_of_ae hAe
  have hPositive :=
    avram_wave6_05_original_positive_countable_w_right_payment_correction_nonpos
      X x C hC q w hw_cont hw_smooth hw_grad
      D hD ω A hCount hA hSummable
  have hZero := avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop
    X x C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
    D hD ω (0 : ℝ≥0) (Or.inl rfl)
  linarith only [hDiffuse, hPositive, hZero]
