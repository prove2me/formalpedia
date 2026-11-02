-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_actual_original_diffuse_positive_jumps_initial_signed_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:04:27.995869+00:00
-- url     : https://prove2.me/submissions/bca185e1-c096-4a21-b125-5aa555af4ad4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_dividend_full_measure_diffuse_strictpre_signed_bridge
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_original_positive_countable_w_right_payment_correction_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

noncomputable section

/-- The actual discounted Stieltjes measure splits into its exact atoms and diffuse
complement, and the diffuse strict-prejump correction, countably many genuine
positive right-payment jumps, and the true initial cap-linear payment residual
have a nonpositive signed sum. No dividend path regularity is assumed. -/
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
    (B : Set ℝ≥0) (hBCount : B.Countable)
    (hB : ∀ t : B, 0 < (t : ℝ≥0) ∧
      ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω)
    (hBWithin : ∀ t : B, (t : ℝ≥0) ≤ T)
    (hSummable : Summable (fun t : B =>
      Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          w (riskProcess X x D (t : ℝ≥0) ω)))) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      ((∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) =
        (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μatom) +
        (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse)) ∧
      ((∀ᵐ s ∂μdiffuse.restrict
          (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)),
        1 ≤ deriv w (x +
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω)) →
        (∫ s in paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ),
          Real.exp (-(q * s)) *
            (1 - deriv w (x +
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
              rightLimit D s.toNNReal ω)) ∂μdiffuse) +
        (∑' t : B, Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
          ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
            w (riskProcess X x D (t : ℝ≥0) ω -
              (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
            w (riskProcess X x D (t : ℝ≥0) ω))) +
        ((rightLimit D 0 ω - D 0 ω) +
          V (riskProcess X x D 0 ω -
            (rightLimit D 0 ω - D 0 ω)) -
          V (riskProcess X x D 0 ω)) ≤ 0) := by
  rcases avram_wave6_05_actual_dividend_full_measure_diffuse_strictpre_signed_bridge
    X x D hD.1 ω T with
    ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit, hAtom,
      hOutside, hNull, hAt, hAll⟩
  refine ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit, hAtom,
    hOutside, hNull, hAt, (hAll q w).1, ?_⟩
  intro hGradient
  have hDiffuse := (hAll q w).2 hGradient
  have hJumps :=
    avram_wave6_05_original_positive_countable_w_right_payment_correction_nonpos
      X x C hC q w hw_cont hw_smooth hw_grad
      D hD ω B hBCount hB hSummable
  have hInitial :=
    avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop
      X x C hC w V hw_cont hw_smooth hw_grad
      hVtop hVfinite D hD ω (0 : ℝ≥0) (Or.inl rfl)
  linarith only [hDiffuse, hJumps, hInitial]
