-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_ubv_same_source_positive_preruin_sigma_finite_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:35:33.221591+00:00
-- url     : https://prove2.me/submissions/1c7b0d3a-3a68-4303-952e-a9985cbdede9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_dividend_strategy_predictable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_original_controlled_preruin_fixed_time_strict_positive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

private theorem jointControlledReserve
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

/-- Under original admissible pre-ruin nonnegativity, true controlled reserve
does not occupy zero for any deterministic sigma-finite time measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (hPreNonneg : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ riskProcess X x D s ω)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (μ : Measure ℝ≥0) [SFinite μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (t : ℝ≥0∞) < ruinTime X x D ω →
        0 < riskProcess X x D t ω := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hUJoint := jointControlledReserve X x D hD
  have hT : Measurable (fun z : ℝ≥0 × Ω => z.1) := measurable_fst
  have hTau : Measurable (fun z : ℝ≥0 × Ω => ruinTime X x D z.2) :=
    (ruinTime_measurable X x D hD).comp measurable_snd
  have hTimeEN : Measurable (fun z : ℝ≥0 × Ω => (z.1 : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp hT
  have hPre : MeasurableSet {z : ℝ≥0 × Ω |
      (z.1 : ℝ≥0∞) < ruinTime X x D z.2} :=
    measurableSet_lt hTimeEN hTau
  have hZero : MeasurableSet {z : ℝ≥0 × Ω |
      riskProcess X x D z.1 z.2 = 0} :=
    hUJoint (measurableSet_singleton (0 : ℝ))
  have hBad : MeasurableSet {z : ℝ≥0 × Ω |
      (z.1 : ℝ≥0∞) < ruinTime X x D z.2 ∧
        riskProcess X x D z.1 z.2 = 0} :=
    hPre.inter hZero
  have hTimeSlices :
      ∀ᵐ (t : ℝ≥0) ∂μ, ∀ᵐ ω ∂P,
      ¬ ((t : ℝ≥0∞) < ruinTime X x D ω ∧
        riskProcess X x D t ω = 0) := by
    apply Filter.Eventually.of_forall
    intro t
    filter_upwards
      [avram_wave4_04_ubv_original_controlled_preruin_fixed_time_strict_positive
        X hBV x D hD hPreNonneg t times horizons hdense hpos hcofinal]
      with ω hPositive
    intro hω
    exact (ne_of_gt (hPositive hω.1)) hω.2
  have hSwap :
      ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      ¬ ((t : ℝ≥0∞) < ruinTime X x D ω ∧
        riskProcess X x D t ω = 0) :=
    (Measure.ae_ae_comm hBad.compl).mp hTimeSlices
  filter_upwards [hSwap] with ω hω
  filter_upwards [hω] with t ht
  intro hpre
  by_contra hnot
  have hzero : riskProcess X x D t ω = 0 :=
    le_antisymm (le_of_not_gt hnot) (hPreNonneg ω t hpre)
  exact ht ⟨hpre, hzero⟩
