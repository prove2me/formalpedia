-- Prove2me | solution 1 for AvramDividend.Classical.ruinTime_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T15:00:15.710851+00:00
-- url     : https://prove2.me/submissions/2b24aab7-42d9-453c-a23a-95793f53e071

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_lt_iff_exists_rat_negative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    Measurable (ruinTime X x D) := by
  apply measurable_of_Iio
  intro a
  have hset :
      (ruinTime X x D) ⁻¹' Iio a =
        ⋃ q : ℚ,
          if hq : 0 ≤ q ∧ (Real.toNNReal q : ℝ≥0∞) < a then
            {ω | riskProcess X x D (Real.toNNReal q) ω < 0}
          else ∅ := by
    ext ω
    simp only [mem_preimage, mem_Iio, mem_iUnion]
    constructor
    · intro hτ
      rcases (ruinTime_lt_iff_exists_rat_negative X x D hD ω a).mp hτ with
        ⟨q, hq0, hqa, hneg⟩
      refine ⟨q, ?_⟩
      simp [hq0, hqa, hneg]
    · rintro ⟨q, hqω⟩
      by_cases hq : 0 ≤ q ∧ (Real.toNNReal q : ℝ≥0∞) < a
      · simp [hq] at hqω
        exact (ruinTime_lt_iff_exists_rat_negative X x D hD ω a).mpr
          ⟨q, hq.1, hq.2, hqω⟩
      · simp [hq] at hqω
  rw [hset]
  apply MeasurableSet.iUnion
  intro q
  split_ifs with hq
  · exact measurableSet_lt
      (riskProcess_measurable X x D hD (Real.toNNReal q)) measurable_const
  · exact MeasurableSet.empty
