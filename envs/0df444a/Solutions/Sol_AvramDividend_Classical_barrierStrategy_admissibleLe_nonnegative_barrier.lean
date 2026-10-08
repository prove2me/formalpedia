-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_admissibleLe_nonnegative_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T13:47:36.834282+00:00
-- url     : https://prove2.me/submissions/8d3d0d0f-6cdb-40c6-aac4-c44b68391f5d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_payment_feasible_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_reserve_cap_nonnegative_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) :
    IsAdmissibleLe X x (ENNReal.ofReal a) (barrierStrategy X x a) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact AvramDividend.Classical.barrierStrategy_isDividendStrategy_nonnegative_barrier
      X x a hx ha
  · exact AvramDividend.Classical.barrierStrategy_payment_feasible_nonnegative_barrier
      X x a hx ha
  · exact AvramDividend.Classical.barrierStrategy_reserve_cap_nonnegative_barrier
      X x a hx ha
