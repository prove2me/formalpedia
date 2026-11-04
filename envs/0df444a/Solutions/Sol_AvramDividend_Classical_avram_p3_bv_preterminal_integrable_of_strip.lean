-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_preterminal_integrable_of_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:32:37.51004+00:00
-- url     : https://prove2.me/submissions/9d9825d4-dd97-4937-b13d-1efc4dc902e6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_continuous_test_abs_le_on_finite_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (hwMeas : Measurable w)
    (Z : Ω → ℝ) (hZ : Measurable Z)
    (A : Set Ω) [DecidablePred (fun ω => ω ∈ A)] (hA : MeasurableSet A)
    (B : ℝ) (hB : 0 ≤ B)
    (hstrip : ∀ᵐ ω ∂P, ω ∈ A → 0 ≤ Z ω ∧ Z ω ≤ B)
    (q T : ℝ) :
    Integrable (fun ω => if ω ∈ A then Real.exp (-(q * T)) * w (Z ω)
      else 0) P := by
  obtain ⟨M, hM, hbound⟩ := continuous_test_abs_le_on_finite_cap w B hB hw
  have hMeas : Measurable (fun ω =>
      if ω ∈ A then Real.exp (-(q * T)) * w (Z ω) else 0) :=
    (measurable_const.mul (hwMeas.comp hZ)).ite hA measurable_const
  have hboundae : ∀ᵐ ω ∂P,
      ‖(if ω ∈ A then Real.exp (-(q * T)) * w (Z ω) else 0 : ℝ)‖ ≤
        Real.exp (-(q * T)) * M := by
    filter_upwards [hstrip] with ω hω
    by_cases hωA : ω ∈ A
    · have hz := hω hωA
      simp only [if_pos hωA, Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hbound (Z ω) hz.1 hz.2)
        (le_of_lt (Real.exp_pos _))
    · simp only [if_neg hωA, norm_zero]
      exact mul_nonneg (le_of_lt (Real.exp_pos _)) hM
  exact (integrable_const (Real.exp (-(q * T)) * M)).mono'
    hMeas.aestronglyMeasurable hboundae
