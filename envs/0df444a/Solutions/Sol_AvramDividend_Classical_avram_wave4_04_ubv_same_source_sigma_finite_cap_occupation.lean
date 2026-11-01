-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:53:11.550336+00:00
-- url     : https://prove2.me/submissions/27febe9e-9ece-402b-9c12-249fd27de4cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_dividend_strategy_predictable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_adapted_capped_reserve_strict_at_fixed_time_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

private theorem jointControlledRisk
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun z : ℝ≥0 × Ω => riskProcess X x D z.1 z.2) := by
  have hPredLe : 𝓕.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
    apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      exact (measurableSet_singleton _).prod ((𝓕.le ⊥) A hA)
    · intro i A hA
      exact measurableSet_Ioi.prod ((𝓕.le i) A hA)
  have hDJoint : Measurable (fun z : ℝ≥0 × Ω => D z.1 z.2) :=
    (avram_wave3_04_dividend_strategy_predictable 𝓕 D hD).mono hPredLe le_rfl
  have hXJoint : Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2) :=
    chat04_levy_joint_time_state_measurable X
  convert (measurable_const.add hXJoint).sub hDJoint using 1 <;> rfl

/-- Genuine finite-cap occupation of original controlled paths, conditional only on
the cap-bound supplied by the source admissibility premise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (μ : Measure ℝ≥0) [SFinite μ]
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c) :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
        riskProcess X x D t ω < c := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hUJoint := jointControlledRisk X x D hD
  have hTime : Measurable (fun z : ℝ≥0 × Ω => z.1) := measurable_fst
  have hRuin : Measurable (fun z : ℝ≥0 × Ω => ruinTime X x D z.2) :=
    (ruinTime_measurable X x D hD).comp measurable_snd
  have hTimeEN : Measurable (fun z : ℝ≥0 × Ω => (z.1 : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp hTime
  have hZero : MeasurableSet {z : ℝ≥0 × Ω | 0 < z.1} :=
    measurableSet_lt measurable_const hTime
  have hPre : MeasurableSet {z : ℝ≥0 × Ω |
      (z.1 : ℝ≥0∞) < ruinTime X x D z.2} :=
    measurableSet_lt hTimeEN hRuin
  have hContact : MeasurableSet {z : ℝ≥0 × Ω |
      riskProcess X x D z.1 z.2 = c} :=
    hUJoint (measurableSet_singleton c)
  have hBad : MeasurableSet {z : ℝ≥0 × Ω |
      0 < z.1 ∧ (z.1 : ℝ≥0∞) < ruinTime X x D z.2 ∧
        riskProcess X x D z.1 z.2 = c} :=
    by simpa only [Set.setOf_and, Set.inter_assoc] using
      (hZero.inter hPre).inter hContact
  have hTimeSlices :
      ∀ᵐ (t : ℝ≥0) ∂μ, ∀ᵐ ω ∂P,
      ¬ (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
        riskProcess X x D t ω = c) := by
    apply Filter.Eventually.of_forall
    intro t
    by_cases ht : 0 < t
    · filter_upwards
        [avram_wave4_04_ubv_adapted_capped_reserve_strict_at_fixed_time_ae
          X hBV x c D hD t ht] with ω hStrict
      intro hBadω
      have hPreT : (t : ℝ≥0∞) < ruinTime X x D ω := hBadω.2.1
      have hPast : ∀ s : ℝ≥0, s ≤ t →
          riskProcess X x D s ω ≤ c := by
        intro s hs
        apply hCap ω s
        exact lt_of_le_of_lt (by exact_mod_cast hs) hPreT
      exact (ne_of_lt (hStrict hPast)) hBadω.2.2
    · exact Filter.Eventually.of_forall (fun ω hBadω => ht hBadω.1)
  have hSwap :
      ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      ¬ (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
        riskProcess X x D t ω = c) :=
    (Measure.ae_ae_comm hBad.compl).mp hTimeSlices
  filter_upwards [hSwap] with ω hω
  filter_upwards [hω] with t ht
  intro hpre
  by_contra hNot
  have hEq : riskProcess X x D t ω = c :=
    le_antisymm (hCap ω t hpre.2) (le_of_not_gt hNot)
  exact ht ⟨hpre.1, hpre.2, hEq⟩
