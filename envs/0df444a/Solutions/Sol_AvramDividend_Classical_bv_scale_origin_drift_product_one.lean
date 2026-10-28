-- Prove2me | solution 1 for AvramDividend.Classical.bv_scale_origin_drift_product_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:35:20.019459+00:00
-- url     : https://prove2.me/submissions/0c74efbf-ac85-4917-94a1-2d3e015512af

import Mathlib.Tactic.FieldSimp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_scale_origin_eq_inv_drift
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The BV scale-function origin value cancels the physical drift boundary term. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) :
    X.drift * W 0 = 1 := by
  have hd : X.drift ≠ 0 := ne_of_gt (bv_standing_drift_pos X hX hbv).1
  rw [bv_scale_origin_eq_inv_drift X hX q hq W hW hbv]
  field_simp
