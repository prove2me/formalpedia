-- Prove2me | solution 1 for AvramDividend.Classical.positive_jump_tail_density_total_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T13:10:16.245201+00:00
-- url     : https://prove2.me/submissions/5d63277c-71cf-4bb5-b89f-bcab33a7bff1

import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- The undiscounted positive-jump tail has total mass equal to the first moment,
even when the measure itself is not sigma-finite. -/
theorem solution (μ : Measure ℝ≥0) :
    ((volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t : ℝ => μ {z : ℝ≥0 | t < (z : ℝ)})) Set.univ =
      ∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ := by
  let tail : ℝ → ℝ≥0∞ := fun t => μ {z : ℝ≥0 | t < (z : ℝ)}
  have htail : Antitone tail := by
    intro x y hxy
    apply measure_mono
    intro z hz
    exact lt_of_le_of_lt hxy hz
  have htail_meas :
      AEMeasurable tail (volume.restrict (Ioi (0 : ℝ))) :=
    htail.measurable.aemeasurable.restrict
  have hf : 0 ≤ᵐ[μ] (fun z : ℝ≥0 => (z : ℝ)) :=
    Filter.Eventually.of_forall (fun z => by positivity)
  have hm : AEMeasurable (fun z : ℝ≥0 => (z : ℝ)) μ :=
    (by fun_prop : Measurable (fun z : ℝ≥0 => (z : ℝ))).aemeasurable
  have hi : ∀ t > 0,
      IntervalIntegrable (fun u : ℝ => (1 : ℝ)) volume 0 t := by
    intro t ht
    exact intervalIntegrable_const
  have hn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall (fun t => by positivity)
  have h_layer :
      (∫⁻ z : ℝ≥0,
        ENNReal.ofReal (∫ t in (0 : ℝ)..(z : ℝ), (1 : ℝ)) ∂μ) =
        ∫⁻ t in Ioi (0 : ℝ),
          μ {z : ℝ≥0 | t < (z : ℝ)} * ENNReal.ofReal (1 : ℝ) := by
    simpa using
      (MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul μ
        (f := fun z : ℝ≥0 => (z : ℝ))
        (g := fun t : ℝ => (1 : ℝ)) hf hm hi hn)
  have hmass :
      (∫⁻ t in Ioi (0 : ℝ), μ {z : ℝ≥0 | t < (z : ℝ)}) =
        ∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ := by
    simpa [intervalIntegral.integral_const] using h_layer.symm
  change ((volume.restrict (Ioi (0 : ℝ))).withDensity tail) Set.univ = _
  rw [withDensity_apply _ MeasurableSet.univ]
  simpa only [Measure.restrict_univ] using hmass
