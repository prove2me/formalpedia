-- Prove2me | solution 1 for AvramDividend.Classical.chat03_scale_function_borel_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:26:08.042147+00:00
-- url     : https://prove2.me/submissions/be5842f6-601e-48e7-bef9-b60ab314d091

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
Borel measurability of the exact q-scale function, including a possible
jump at zero in the bounded-variation case. This discharges the remaining
measurability assumption in the stopped-scale L² estimate once the
bounded-grid stop and sampled X are themselves measurable.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Measurable W := by
  classical
  have hm : Measurable
      ((Ici (0 : ℝ)).piecewise W (fun _ => 0)) :=
    hW.2.2.1.measurable_piecewise continuousOn_const measurableSet_Ici
  have heq : (Ici (0 : ℝ)).piecewise W (fun _ => 0) = W := by
    funext y
    by_cases hy : 0 ≤ y
    · simp [Set.piecewise, hy]
    · have hneg : y < 0 := lt_of_not_ge hy
      have hz : W y = 0 := hW.1 y hneg
      simp [Set.piecewise, hy, hz]
  simpa only [heq] using hm