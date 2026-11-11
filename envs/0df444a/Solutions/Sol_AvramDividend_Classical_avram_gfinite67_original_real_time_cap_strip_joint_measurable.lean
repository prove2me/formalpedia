-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite67_original_real_time_cap_strip_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:10:58.147601+00:00
-- url     : https://prove2.me/submissions/26166d7e-8b66-4961-a626-40d0f646d97a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_dividend_strategy_predictable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (b : ℝ) :
    MeasurableSet {z : ℝ × Ω |
      z.1 < (ρ z.2 : ℝ) ∧
        b < riskProcess X x D (Real.toNNReal z.1) z.2} := by
  have hPredLe : 𝓕.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
    apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      exact (measurableSet_singleton _).prod ((𝓕.le ⊥) A hA)
    · intro i A hA
      exact measurableSet_Ioi.prod ((𝓕.le i) A hA)
  have hDJoint : Measurable
      (fun z : ℝ≥0 × Ω => D z.1 z.2) :=
    (avram_wave3_04_dividend_strategy_predictable 𝓕 D hD).mono
      hPredLe le_rfl
  have hXJoint : Measurable
      (fun z : ℝ≥0 × Ω => X.X z.1 z.2) :=
    chat04_levy_joint_time_state_measurable X
  have hRisk : Measurable
      (fun z : ℝ≥0 × Ω => riskProcess X x D z.1 z.2) := by
    convert (measurable_const.add hXJoint).sub hDJoint using 1 <;> rfl
  have hPair : Measurable
      (fun z : ℝ × Ω => (Real.toNNReal z.1, z.2)) :=
    (Measurable.real_toNNReal measurable_fst).prodMk measurable_snd
  have hRho : Measurable (fun ω : Ω => (ρ ω : ℝ)) :=
    avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
      ρ hρstop
  have hRhoPair : Measurable (fun z : ℝ × Ω => (ρ z.2 : ℝ)) :=
    hRho.comp measurable_snd
  have hTime : MeasurableSet
      {z : ℝ × Ω | z.1 < (ρ z.2 : ℝ)} :=
    measurableSet_lt measurable_fst hRhoPair
  have hState : MeasurableSet
      {z : ℝ × Ω | b < riskProcess X x D (Real.toNNReal z.1) z.2} :=
    measurableSet_lt measurable_const (hRisk.comp hPair)
  exact hTime.inter hState
