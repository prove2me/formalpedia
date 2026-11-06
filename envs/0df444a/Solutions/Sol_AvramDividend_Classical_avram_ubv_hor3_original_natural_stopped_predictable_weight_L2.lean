-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_natural_stopped_predictable_weight_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:22:40.315864+00:00
-- url     : https://prove2.me/submissions/7af66e07-06f9-487a-8463-f4a663f8c62e

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

/-- True clipped-ruin mask preserves square integrability of physical grid weights. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (Cap : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x Cap D)
    (n : ℕ) (grid : ℕ → ℝ≥0)
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P) :
    ∃ τ : Ω → ℝ≥0,
      (∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) ∧
      (∀ i, MemLp
        (fun ω => if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H i ω) 2 P) := by
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
  have hSM : StronglyMeasurable[𝓕.rightCont (grid i)]
      (fun ω => if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω) :=
    (stronglyMeasurable_const).ite hSet (hH i)
  have hSMGlobal : StronglyMeasurable (fun ω =>
      if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0) then (0 : ℝ) else H i ω) :=
    hSM.mono ((𝓕.rightCont).le (grid i))
  apply (hHL2 i).of_le hSMGlobal.aestronglyMeasurable
  filter_upwards [] with ω
  change ‖(if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H i ω)‖ ≤ ‖H i ω‖
  by_cases h : (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
  · simpa only [if_pos h, norm_zero] using (norm_nonneg (H i ω))
  · simpa only [if_neg h] using (le_refl (‖H i ω‖))
