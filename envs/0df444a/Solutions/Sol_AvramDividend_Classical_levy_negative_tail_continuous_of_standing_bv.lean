-- Prove2me | solution 1 for AvramDividend.Classical.levy_negative_tail_continuous_of_standing_bv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:21:15.251881+00:00
-- url     : https://prove2.me/submissions/a38e95d3-3d80-4670-9f67-e25b50aa9c3e

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.ContinuousOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyMeasure_singleton_null_of_standing_boundedVariation
import Theorems.Thm_AvramDividend_Classical_levy_negative_mass_away_from_zero_finite
import Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Iic_negative_of_finite_noAtoms

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped ENNReal NNReal

/-- The negative jump tail is continuous away from the Lévy singularity at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) :
    ContinuousOn (fun r : ℝ => X.ν.real (Iic (-r))) (Ioi (0 : ℝ)) := by
  letI : NullSingletonClass X.ν :=
    ⟨fun a => levyMeasure_singleton_null_of_standing_boundedVariation X hX hbv a⟩
  have hfinite : ∀ a : ℝ, a < 0 → X.ν (Iic a) ≠ ⊤ := by
    intro a ha
    have hδ : 0 < -a := by linarith
    have h := levy_negative_mass_away_from_zero_finite X (-a) hδ
    have hbound : X.ν (Iic a) < ⊤ := by simpa using h
    exact ne_of_lt hbound
  have hcont : ContinuousOn (fun a : ℝ => X.ν.real (Iic a)) (Iio 0) :=
    continuousOn_measureReal_Iic_negative_of_finite_noAtoms X.ν hfinite
  have hneg : ContinuousOn (fun r : ℝ => -r) (Ioi (0 : ℝ)) :=
    (continuous_id.neg).continuousOn
  have hmaps : MapsTo (fun r : ℝ => -r) (Ioi (0 : ℝ)) (Iio (0 : ℝ)) := by
    intro r hr
    change -r < 0
    exact neg_lt_zero.mpr hr
  exact hcont.comp hneg hmaps
