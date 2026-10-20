-- Prove2me | solution 1 for AvramDividend.Classical.ruinTime_strict_event_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:44:52.65404+00:00
-- url     : https://prove2.me/submissions/83346d4e-451c-403b-9ce7-68e5d73e04a6

import Mathlib.Probability.Process.Filtration
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_adapted
import Theorems.Thm_AvramDividend_Classical_ruinTime_lt_iff_exists_rat_negative

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (t : ℝ≥0) :
    MeasurableSet[𝓕 t] {ω | ruinTime X x D ω < (t : ℝ≥0∞)} := by
  let Q := {q : ℚ // 0 ≤ q ∧
    (Real.toNNReal (q : ℝ) : ℝ≥0∞) < (t : ℝ≥0∞)}
  have hset : {ω : Ω | ruinTime X x D ω < (t : ℝ≥0∞)} =
      ⋃ q : Q, {ω : Ω |
        riskProcess X x D (Real.toNNReal (q : ℝ)) ω < 0} := by
    ext ω
    constructor
    · intro hω
      obtain ⟨q, hq0, hqt, hneg⟩ :=
        (ruinTime_lt_iff_exists_rat_negative X x D hD ω (t : ℝ≥0∞)).mp hω
      exact Set.mem_iUnion.mpr ⟨⟨q, hq0, hqt⟩, hneg⟩
    · intro hω
      obtain ⟨q, hneg⟩ := Set.mem_iUnion.mp hω
      exact (ruinTime_lt_iff_exists_rat_negative X x D hD ω
        (t : ℝ≥0∞)).mpr ⟨(q : ℚ), q.property.1, q.property.2, hneg⟩
  rw [hset]
  apply MeasurableSet.iUnion
  intro q
  have hqle : Real.toNNReal (q : ℝ) ≤ t :=
    ENNReal.coe_le_coe.mp q.property.2.le
  have h_adapt : Measurable[𝓕 (Real.toNNReal (q : ℝ))]
      (riskProcess X x D (Real.toNNReal (q : ℝ))) :=
    riskProcess_adapted X x D hD _
  have h_measure : Measurable[𝓕 t]
      (riskProcess X x D (Real.toNNReal (q : ℝ))) :=
    h_adapt.mono (𝓕.mono hqle) le_rfl
  exact h_measure measurableSet_Iio
