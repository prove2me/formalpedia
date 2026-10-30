-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_two_sided_grid_scale_square_meas
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:43:45.210413+00:00
-- url     : https://prove2.me/submissions/77b76472-3806-46ce-97da-5ec306e31016

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat03_grid_stopped_reserve_time_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine source two-sided grid stopped q-scale squared payoff
is strongly measurable under the original Levy probability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ)
    (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω) :
    AEStronglyMeasurable (fun ω =>
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2) P := by
  obtain ⟨hZ, hT⟩ :=
    chat03_grid_stopped_reserve_time_measurable
      X clock H hH lower upper m K hK
  have hWm : Measurable W :=
    chat04_scaleFunction_measurable_of_punctured_continuity X q W hW
  have hExp : Measurable (fun ω =>
      Real.exp (-(q * (clock (K ω) : ℝ)))) :=
    Real.continuous_exp.measurable.comp
      ((measurable_const.mul hT).neg)
  have hScale : Measurable (fun ω =>
      W (x + X.X (clock (K ω)) ω)) :=
    hWm.comp (measurable_const.add hZ)
  exact ((hExp.mul hScale).pow_const 2).aestronglyMeasurable
