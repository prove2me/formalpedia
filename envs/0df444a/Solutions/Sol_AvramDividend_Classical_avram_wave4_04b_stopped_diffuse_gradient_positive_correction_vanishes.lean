-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_stopped_diffuse_gradient_positive_correction_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:32:55.528825+00:00
-- url     : https://prove2.me/submissions/a5bd0766-217a-42ff-ba0e-1ebeb6e17a98

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
/-- At every strictly interior paid time the signed continuous dividend
correction is nonpositive; this remains true when integrated against
an arbitrary atomless (possibly singular-continuous) Stieltjes measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞) (q : ℝ)
    (ν : Measure ℝ) [NullSingletonClass ν]
    (hloc : ∀ t : ℝ≥0, t ≤ T → (t : ℝ) ∈ paymentTimes τ →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C) :
    (∫⁻ s in paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal
        (Real.exp (-q * s) *
          (1 - deriv w (riskProcess X x D s.toNNReal ω))) ∂ν) = 0 := by
  let E : Set ℝ := paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ)
  have hMeas : MeasurableSet E :=
    (paymentTimes_measurable τ).inter measurableSet_Icc
  have hzero : ∀ s : ℝ, s ∈ E →
      ENNReal.ofReal
        (Real.exp (-q * s) *
          (1 - deriv w (riskProcess X x D s.toNNReal ω))) = 0 := by
    intro s hs
    have hs' : s ∈ paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ) := hs
    have hcoe : ((s.toNNReal : ℝ≥0) : ℝ) = s :=
      Real.coe_toNNReal s hs'.2.1
    have ht : s.toNNReal ≤ T := by
      exact_mod_cast (show (((s.toNNReal : ℝ≥0) : ℝ) ≤ (T : ℝ)) from by
        simpa only [hcoe] using hs'.2.2)
    have hReserve := hloc s.toNNReal ht (by simpa only [hcoe] using hs'.1)
    have hg := hw_grad (riskProcess X x D s.toNNReal ω)
      hReserve.1 hReserve.2
    have hdiff : 1 - deriv w (riskProcess X x D s.toNNReal ω) ≤ 0 := by
      linarith
    have hnonpos :
        Real.exp (-q * s) *
          (1 - deriv w (riskProcess X x D s.toNNReal ω)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hdiff
    exact ENNReal.ofReal_eq_zero.mpr hnonpos
  calc
    (∫⁻ s in paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal
        (Real.exp (-q * s) *
          (1 - deriv w (riskProcess X x D s.toNNReal ω))) ∂ν) =
      (∫⁻ s : ℝ, E.indicator
        (fun s : ℝ => ENNReal.ofReal
          (Real.exp (-q * s) *
            (1 - deriv w (riskProcess X x D s.toNNReal ω)))) s ∂ν) := by
        exact (lintegral_indicator hMeas _).symm
    _ = (∫⁻ s : ℝ, (0 : ℝ≥0∞) ∂ν) := by
      apply lintegral_congr
      intro s
      by_cases hs : s ∈ E
      · have hz := hzero s hs
        simpa only [Set.indicator_of_mem hs, neg_mul] using hz
      · simp [Set.indicator, hs]
    _ = 0 := by simp
