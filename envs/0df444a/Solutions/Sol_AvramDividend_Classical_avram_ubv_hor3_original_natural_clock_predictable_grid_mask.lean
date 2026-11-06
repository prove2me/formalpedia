-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_natural_clock_predictable_grid_mask
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:57:36.013195+00:00
-- url     : https://prove2.me/submissions/6234900b-759a-4f19-abf4-be5a9b0fbebf

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source-exact predictable pre-ruin mask for the original stopped reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (Cap : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x Cap D)
    (n : ℕ) (grid : ℕ → ℝ≥0)
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i)) :
    ∃ τ : Ω → ℝ≥0,
      (∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) ∧
      (∀ i, StronglyMeasurable[𝓕.rightCont (grid i)]
        (fun ω => if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H i ω)) := by
  have hDS : IsDividendStrategy 𝓕 D := hD.1.1
  have hRuinMeas : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hDS
  have hRuinStop : IsStoppingTime 𝓕.rightCont (ruinTime X x D) :=
    ruinTime_stopping_rightCont_filtration X x D hDS
  obtain ⟨τ, hτEq, _, hτStop⟩ :=
    avram_wave7_08_source_finite_clock_witness_of_ruin_meas_stopping
      X x D n hRuinMeas hRuinStop
  refine ⟨τ, hτEq, ?_⟩
  intro i
  have hSet : MeasurableSet[𝓕.rightCont (grid i)]
      {ω : Ω | (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)} :=
    hτStop.measurableSet_le (grid i)
  exact (stronglyMeasurable_const).ite hSet (hH i)
