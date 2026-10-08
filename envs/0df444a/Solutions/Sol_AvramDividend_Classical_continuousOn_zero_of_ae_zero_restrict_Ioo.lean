-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_zero_of_ae_zero_restrict_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T10:56:55.518287+00:00
-- url     : https://prove2.me/submissions/7a07e699-d6ab-4324-aaae-a9a5162f269f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_continuousAt_eq_zero_of_ae_zero_at_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (f : ℝ → ℝ) (a : ℝ)
    (hcont : ContinuousOn f (Ioo 0 a))
    (hae : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo 0 a)),
      f x = 0) :
    ∀ x ∈ Ioo 0 a, f x = 0 := by
  intro x hx
  have hxInterior : x ∈ interior (Ioo (0 : ℝ) a) := by
    simpa [isOpen_Ioo.interior_eq] using hx
  have hxSupport :
      x ∈ ((volume : Measure ℝ).restrict (Ioo 0 a)).support := by
    apply Measure.interior_inter_support (μ := (volume : Measure ℝ))
    exact ⟨hxInterior, by simpa [Measure.support_eq_univ]⟩
  exact continuousAt_eq_zero_of_ae_zero_at_support
    ((volume : Measure ℝ).restrict (Ioo 0 a)) f x hxSupport
    (hcont.continuousAt (isOpen_Ioo.mem_nhds hx)) hae
