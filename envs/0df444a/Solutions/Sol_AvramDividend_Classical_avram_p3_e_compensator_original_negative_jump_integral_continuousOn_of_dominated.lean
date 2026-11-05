-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_original_negative_jump_integral_continuousOn_of_dominated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:32:05.133985+00:00
-- url     : https://prove2.me/submissions/31894165-5074-4991-8a42-e1f3e4baa8ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Dominated continuity of the original Lévy negative-jump generator integral. -/
theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
(w : ℝ → ℝ) (a b : ℝ) (bound : ℝ → ℝ)
(hMeas : ∀ y ∈ Set.Icc a b, AEStronglyMeasurable
  (fun z : ℝ => w (y + z) - w y) (X.ν.restrict (Set.Iio (0 : ℝ))))
(hBound : ∀ y ∈ Set.Icc a b, ∀ᵐ z ∂(X.ν.restrict (Set.Iio (0 : ℝ))),
  ‖w (y + z) - w y‖ ≤ bound z)
(hBoundInt : Integrable bound (X.ν.restrict (Set.Iio (0 : ℝ))))
(hCont : ∀ᵐ z ∂(X.ν.restrict (Set.Iio (0 : ℝ))),
  ContinuousOn (fun y : ℝ => w (y + z) - w y) (Set.Icc a b)) :
ContinuousOn (fun y : ℝ =>
  ∫ z in Set.Iio (0 : ℝ), w (y + z) - w y ∂X.ν) (Set.Icc a b) := by
  exact MeasureTheory.continuousOn_of_dominated hMeas hBound hBoundInt hCont
