-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_true_preruin_complete_signed_stieltjes_control_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:40:58.953634+00:00
-- url     : https://prove2.me/submissions/e38d73ab-5075-42cd-98fe-875912f2d72e

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_true_preruin_stopped_right_payment_signed_correction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_stopped_atomless_signed_continuous_correction_nonpos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

/-- The complete signed finite-variation control correction has its source
chronological sign for genuine pre-ruin payments and all atomless measures. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q)
    (ν : Measure ℝ) [NullSingletonClass ν]
    (A : Set ℝ)
    (hA : A = {s : ℝ | s ∈ paymentTimes (ruinTime X x D ω) ∧
      s ≤ (T : ℝ) ∧ 0 < rightLimit D s.toNNReal ω - D s.toNNReal ω})
    (L : ℝ) (hL : 0 ≤ L)
    (hjump : ∀ t : ℝ≥0,
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (hSecant : ∀ s : A,
      |(rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) +
        w (riskProcess X x D ((s : ℝ).toNNReal) ω -
          (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) -
        w (riskProcess X x D ((s : ℝ).toNNReal) ω)| ≤
      L * (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω))
    (hloc : ∀ t : ℝ≥0, t ≤ T →
      (t : ℝ) ∈ paymentTimes (ruinTime X x D ω) →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C)
    (hIntegrable : IntegrableOn
      (fun s : ℝ => Real.exp (-q * s) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)))
      (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)) ν) :
    (∫ s in paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ),
      Real.exp (-q * s) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂ν) +
    (∑' s : A, Real.exp (-(q * (s : ℝ))) *
      ((rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) +
        w (riskProcess X x D ((s : ℝ).toNNReal) ω -
          (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) -
        w (riskProcess X x D ((s : ℝ).toNNReal) ω))) ≤ 0 := by
  have hAtoms :=
    avram_wave4_04b_true_preruin_stopped_right_payment_signed_correction
      X x D hD w ω T q hq A hA L hL hjump hSecant
  apply add_nonpos
  · exact avram_wave4_04b_stopped_atomless_signed_continuous_correction_nonpos
      X x D hD w C hw_grad ω T (ruinTime X x D ω) q ν hloc hIntegrable
  · exact hAtoms.2
