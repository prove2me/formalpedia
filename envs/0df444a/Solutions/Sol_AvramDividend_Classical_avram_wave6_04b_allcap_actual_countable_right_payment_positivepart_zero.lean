-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04b_allcap_actual_countable_right_payment_positivepart_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:39:34.818557+00:00
-- url     : https://prove2.me/submissions/f0daa9c4-f4bd-4428-b573-e243c5665445

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_allcap_actual_right_payment_secant_nonpos

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- All chronological actual right-dividend V-corrections have zero
discounted ENNReal positive-part tsum for arbitrary stopped real-clock sets.
This includes the countable atom support, time zero and boundary contacts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (q : ℝ)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y
        else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (A : Set ℝ)
    (hA : ∀ s : A, (s : ℝ) ∈ paymentTimes (ruinTime X x D ω)) :
    (∑' s : A, ENNReal.ofReal
      (Real.exp (-(q * (s : ℝ))) *
        ((rightLimit D ((s : ℝ).toNNReal) ω -
            D ((s : ℝ).toNNReal) ω) +
          V (riskProcess X x D ((s : ℝ).toNNReal) ω -
            (rightLimit D ((s : ℝ).toNNReal) ω -
              D ((s : ℝ).toNNReal) ω)) -
          V (riskProcess X x D ((s : ℝ).toNNReal) ω)))) = 0 := by
  have hz : (fun s : A => ENNReal.ofReal
      (Real.exp (-(q * (s : ℝ))) *
        ((rightLimit D ((s : ℝ).toNNReal) ω -
            D ((s : ℝ).toNNReal) ω) +
          V (riskProcess X x D ((s : ℝ).toNNReal) ω -
            (rightLimit D ((s : ℝ).toNNReal) ω -
              D ((s : ℝ).toNNReal) ω)) -
          V (riskProcess X x D ((s : ℝ).toNNReal) ω)))) =
      (fun _ => (0 : ℝ≥0∞)) := by
    funext s
    have hs := hA s
    change (s : ℝ) ∈ Ici (0 : ℝ) ∩
      ({0} ∪ {t : ℝ | ENNReal.ofReal t < ruinTime X x D ω}) at hs
    have hPre : ((s : ℝ).toNNReal) = 0 ∨
        (((s : ℝ).toNNReal) : ℝ≥0∞) < ruinTime X x D ω := by
      rcases hs.2 with hzero | hlt
      · left
        have heq : (s : ℝ) = 0 := by simpa using hzero
        simp only [heq, Real.toNNReal_zero]
      · right
        change (((s : ℝ).toNNReal) : ℝ≥0∞) < ruinTime X x D ω at hlt
        exact hlt
    have hsign := avram_wave6_04b_allcap_actual_right_payment_secant_nonpos
      X x C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
      D hD ω ((s : ℝ).toNNReal) hPre
    exact ENNReal.ofReal_eq_zero.mpr
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hsign)
  simpa [hz]
