-- Prove2me | solution 1 for AvramDividend.Classical.chat04_scale_ratio_within_unit_interval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:03:21.165935+00:00
-- url     : https://prove2.me/submissions/9866d19e-ff47-41bb-b409-d949e5f24936

import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The canonical scale ratio for a reserve inside a positive barrier lies in [0,1]. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a x : ℝ)
    (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    0 ≤ W x / W a ∧ W x / W a ≤ 1 := by
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hWx : 0 ≤ W x := hW.2.1 x hx0
  have hWA : W x ≤ W a :=
    hW.2.2.2.1 (Set.mem_Ici.mpr hx0) (Set.mem_Ici.mpr (le_of_lt ha)) hxa
  constructor
  · exact div_nonneg hWx (le_of_lt hWa)
  · exact (div_le_one hWa).2 hWA
