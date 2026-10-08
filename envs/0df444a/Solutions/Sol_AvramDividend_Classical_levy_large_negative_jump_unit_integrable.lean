-- Prove2me | solution 1 for AvramDividend.Classical.levy_large_negative_jump_unit_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T22:34:19.360495+00:00
-- url     : https://prove2.me/submissions/b3d903ea-d4e4-47ed-919d-2aee4a940cc7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic (-1 : ℝ)) X.ν := by
  have hmin_meas : Measurable (fun y : ℝ => min 1 (y ^ 2)) := by fun_prop
  have hmin_nonneg : 0 ≤ᵐ[X.ν] (fun y : ℝ => min 1 (y ^ 2)) :=
    Filter.Eventually.of_forall (fun y =>
      le_min (by norm_num) (sq_nonneg y))
  have hmin_int : Integrable (fun y : ℝ => min 1 (y ^ 2)) X.ν :=
    (lintegral_ofReal_ne_top_iff_integrable
      hmin_meas.aestronglyMeasurable hmin_nonneg).mp
      (ne_of_lt X.ν_integrable)
  have hres : IntegrableOn (fun y : ℝ => min 1 (y ^ 2))
      (Iic (-1 : ℝ)) X.ν := hmin_int.restrict
  refine hres.congr_fun ?_ measurableSet_Iic
  intro y hy
  have hy2 : (1 : ℝ) ≤ y ^ 2 := by
    have hy' : y ≤ -1 := hy
    nlinarith [sq_nonneg (y + 1)]
  simp only [min_eq_left hy2]
