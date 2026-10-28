-- Prove2me | solution 1 for AvramDividend.Classical.bv_standing_negative_jump_intensity_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:31:42.28293+00:00
-- url     : https://prove2.me/submissions/718318bf-5fdf-4393-96cd-4c7b2bb03ce3

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    0 < X.ν (Iio (0 : ℝ)) := by 
  rw [pos_iff_ne_zero]
  intro h0
  apply hX.1
  refine ⟨hBV, Or.inr ?_⟩
  rw [← Measure.measure_univ_eq_zero, ← Iio_union_Ici (a := (0:ℝ))]
  exact le_antisymm ((measure_union_le _ _).trans (by rw [h0, X.ν_Ici, add_zero])) zero_le
