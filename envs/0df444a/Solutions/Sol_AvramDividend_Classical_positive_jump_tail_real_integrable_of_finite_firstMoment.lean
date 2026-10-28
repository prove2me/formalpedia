-- Prove2me | solution 1 for AvramDividend.Classical.positive_jump_tail_real_integrable_of_finite_firstMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T08:27:54.67728+00:00
-- url     : https://prove2.me/submissions/6342527b-727f-4cf6-81d0-32bd957c843a

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A finite first jump-magnitude moment makes the real strict positive tail
    integrable on the positive half-line via the exact layer-cake mass identity. -/
theorem solution
    (μ : Measure ℝ≥0)
    (hfirst : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ) < ⊤) :
    IntegrableOn (fun t : ℝ =>
      (μ {z : ℝ≥0 | t < (z : ℝ)}).toReal) (Ioi (0 : ℝ)) volume := by
  let tail : ℝ → ℝ≥0∞ := fun t => μ {z : ℝ≥0 | t < (z : ℝ)}
  have hanti : Antitone tail := by
    intro x y hxy
    apply measure_mono
    intro z hz
    exact lt_of_le_of_lt hxy hz
  have hmeas :
      AEMeasurable tail (volume.restrict (Ioi (0 : ℝ))) :=
    hanti.measurable.aemeasurable.restrict
  have hmass := positive_jump_tail_density_total_mass μ
  rw [withDensity_apply _ MeasurableSet.univ] at hmass
  have heq :
      (∫⁻ t in Ioi (0 : ℝ), tail t) =
        (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ) := by
    simpa only [Measure.restrict_univ, tail] using hmass
  have hfinite : (∫⁻ t in Ioi (0 : ℝ), tail t) ≠ ⊤ := by
    rw [heq]
    exact ne_of_lt hfirst
  exact integrable_toReal_of_lintegral_ne_top hmeas hfinite
