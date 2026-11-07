-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_nonint_C1_masked_derivative_factor_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:57:02.113364+00:00
-- url     : https://prove2.me/submissions/7619a950-7214-4578-95d6-d919917a412e

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.SetSemiring
import Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_C1_deriv_zero_extension_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
noncomputable section

/-- A measurable zero extension of the derivative yields every measurable
interior-event mask after measurable prestate composition. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (w : ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s)
    (hw : ContDiffOn ℝ 1 w s) (Z : Ω → ℝ) (hZ : Measurable Z)
    (E : Set Ω) (hE : MeasurableSet E)
    (hEi : ∀ ω ∈ E, Z ω ∈ s) (a : ℝ) :
    Measurable (fun ω => if ω ∈ E then a * deriv w (Z ω) else 0) := by
  have hExt : Measurable (fun y : ℝ => if y ∈ s then deriv w y else 0) :=
    avram_a19_nonint_C1_deriv_zero_extension_measurable w s hs hw
  have hComp : Measurable (fun ω : Ω =>
      if Z ω ∈ s then deriv w (Z ω) else 0) := hExt.comp hZ
  have hMasked : Measurable (fun ω : Ω =>
      if ω ∈ E then a * (if Z ω ∈ s then deriv w (Z ω) else 0) else 0) :=
    Measurable.ite hE (measurable_const.mul hComp) measurable_const
  convert hMasked using 1
  funext ω
  by_cases hω : ω ∈ E
  · simp [hω, hEi ω hω]
  · simp [hω]
