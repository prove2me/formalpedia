-- Prove2me | solution 1 for AvramDividend.Classical.riskProcess_nonnegative_strictly_before_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:57:14.872092+00:00
-- url     : https://prove2.me/submissions/df1315e8-6356-4169-8025-b8c0fd27f54b

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ riskProcess X x D t ω := by
  by_contra hnot
  have hneg : riskProcess X x D t ω < 0 :=
    lt_of_not_ge hnot
  have hle : ruinTime X x D ω ≤ (t : ℝ≥0∞) := by
    unfold ruinTime
    exact iInf_le_of_le t (iInf_le _ hneg)
  exact (not_lt_of_ge hle) ht
