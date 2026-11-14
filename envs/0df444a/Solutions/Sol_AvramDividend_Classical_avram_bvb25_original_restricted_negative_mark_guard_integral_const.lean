-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb25_original_restricted_negative_mark_guard_integral_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:57:41.893507+00:00
-- url     : https://prove2.me/submissions/2dc26cbf-f99c-48fa-a51e-ccc35febe916

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) :
    (∫ z : ℝ, (if z < 0 then a else 0) ∂(X.ν.restrict (Iio (0 : ℝ)))) =
      a * (X.ν (Iio (0 : ℝ))).toReal  := by
  have hMem : ∀ᵐ z : ℝ ∂(X.ν.restrict (Iio (0 : ℝ))), z < 0 := by
    simpa only [Set.mem_Iio] using
      (ae_restrict_mem (μ := X.ν) (measurableSet_Iio : MeasurableSet (Iio (0 : ℝ))))
  have hEq : (fun z : ℝ => if z < 0 then a else 0) =ᵐ[X.ν.restrict (Iio (0 : ℝ))]
      (fun _ => a) := by
    filter_upwards [hMem] with z hz
    simp only [if_pos hz]
  rw [integral_congr_ae hEq]
  simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]
  ring
