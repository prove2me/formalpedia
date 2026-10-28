-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_global_continuous_of_zero_origin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:17:21.154132+00:00
-- url     : https://prove2.me/submissions/7567f173-9559-4e90-95dc-2114c836e404

import Mathlib.Topology.ContinuousOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hZero : W 0 = 0) :
    Continuous W := by
  have he : W = fun x => W (max x 0) := by
    funext x
    rcases lt_or_ge x 0 with h | h
    · rw [max_eq_right h.le, hZero, hW.1 x h]
    · rw [max_eq_left h]
  rw [he]
  exact hW.2.2.1.comp_continuous (continuous_id.max continuous_const) (fun x => le_max_right x 0)
