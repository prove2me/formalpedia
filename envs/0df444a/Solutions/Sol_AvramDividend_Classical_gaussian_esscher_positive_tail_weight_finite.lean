-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_positive_tail_weight_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:36:48.612723+00:00
-- url     : https://prove2.me/submissions/3d9071c2-8afc-4f05-872b-2e30ea6cc9b1

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_positive_tail_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- The Esscher exponential is integrable on every positive Lévy tail. -/
theorem solution (μ : Measure ℝ) (ε φ : ℝ) (hε : 0 < ε) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z in Ici ε, ENNReal.ofReal (Real.exp (-φ * z)) ∂μ) < ⊤ := by
  have htail :=
    AvramDividend.Classical.gaussian_levy_positive_tail_finite μ ε hε hlevy
  have hbound :
      (∫⁻ z in Ici ε, ENNReal.ofReal (Real.exp (-φ * z)) ∂μ) ≤
        (∫⁻ z in Ici ε, (1 : ENNReal) ∂μ) := by
    apply lintegral_mono_ae
    filter_upwards
      [ae_restrict_mem (μ := μ) (measurableSet_Ici : MeasurableSet (Ici ε))]
      with z hz
    have hz0 : 0 ≤ z := le_trans hε.le hz
    have hneg : -(φ * z) ≤ 0 :=
      neg_nonpos.mpr (mul_nonneg hφ.le hz0)
    have hexp : Real.exp (-φ * z) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      simpa only [neg_mul] using hneg
    simpa using (ENNReal.ofReal_le_ofReal hexp)
  have hconst : (∫⁻ z in Ici ε, (1 : ENNReal) ∂μ) =
      μ (Ici ε) := by simp
  rw [hconst] at hbound
  exact lt_of_le_of_lt hbound htail
