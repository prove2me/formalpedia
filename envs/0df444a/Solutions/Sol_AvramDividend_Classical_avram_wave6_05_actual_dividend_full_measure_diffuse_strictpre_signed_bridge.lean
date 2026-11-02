-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_actual_dividend_full_measure_diffuse_strictpre_signed_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:50:11.375051+00:00
-- url     : https://prove2.me/submissions/3579d8f1-b5ba-4cec-a3a1-1369ea450586

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_actual_dividend_diffuse_derivative_prejump_stieltjes_integral_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The actual original Stieltjes measure supplies one common atomic and
diffuse witness; the true strict-prejump diffuse gradient has signed cash
domination a.e., including singular-continuous dividend payments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (ω : Ω) (T : ℝ≥0) :
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
      (∀ (q : ℝ) (w : ℝ → ℝ),
        (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) =
          (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μatom) +
          (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse) ∧
        ((∀ᵐ s ∂μdiffuse.restrict
            (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)),
          1 ≤ deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω)) →
          (∫ s in paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ),
            Real.exp (-(q * s)) *
              (1 - deriv w (x +
                Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
                rightLimit D s.toNNReal ω)) ∂μdiffuse) ≤ 0)) := by
  rcases avram_wave4_04b_actual_dividend_diffuse_derivative_prejump_stieltjes_integral_eq
    X x D hD.1 ω T with
    ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit, hAtom,
      hOutside, hNull, hAt, _hMass, _hPreEq⟩
  refine ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit, hAtom,
    hOutside, hNull, hAt, ?_⟩
  intro q w
  constructor
  · rw [hSplit]
    exact MeasureTheory.lintegral_add_measure
      (fun s : ℝ => ENNReal.ofReal (Real.exp (-(q * s))))
      μatom μdiffuse
  · intro hGradient
    have hAe :
        ∀ᵐ s ∂μdiffuse.restrict
          (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)),
          Real.exp (-(q * s)) *
            (1 - deriv w (x +
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
              rightLimit D s.toNNReal ω)) ≤ 0 := by
      filter_upwards [hGradient] with s hs
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
    change (∫ s : ℝ, Real.exp (-(q * s)) *
      (1 - deriv w (x +
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω))
      ∂μdiffuse.restrict
        (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ))) ≤ 0
    exact integral_nonpos_of_ae hAe
