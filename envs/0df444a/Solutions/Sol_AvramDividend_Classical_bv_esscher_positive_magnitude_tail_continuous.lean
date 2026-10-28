-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_positive_magnitude_tail_continuous
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:18:14.447464+00:00
-- url     : https://prove2.me/submissions/63e64121-9e79-4bca-8b80-a270810a7fed

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyMeasure_singleton_null_of_standing_boundedVariation
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_signed_jump_tail_map_identity
import Theorems.Thm_AvramDividend_Classical_levy_esscher_negative_tail_continuous_of_standing_bv
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (φ : ℝ) (hφ : 0 ≤ φ) :
    ContinuousOn (fun r : ℝ =>
      ((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
        (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))).real
        {z : ℝ≥0 | r < (z : ℝ)}) (Ioi (0 : ℝ)) := by
  refine (AvramDividend.Classical.levy_esscher_negative_tail_continuous_of_standing_bv
    X hX hbv φ hφ).congr ?_
  intro r hr
  simp only [Measure.real]
  rw [AvramDividend.Classical.esscher_weighted_signed_jump_tail_map_identity X.ν φ r hr]
  congr 1
  set μ := X.ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))
  have h0 : μ {-r} = 0 := withDensity_absolutelyContinuous _ _
    (AvramDividend.Classical.levyMeasure_singleton_null_of_standing_boundedVariation
      X hX hbv (-r))
  refine le_antisymm (measure_mono Iio_subset_Iic_self) ?_
  rw [← Iio_union_right]
  exact (measure_union_le _ _).trans (by simp [h0])
