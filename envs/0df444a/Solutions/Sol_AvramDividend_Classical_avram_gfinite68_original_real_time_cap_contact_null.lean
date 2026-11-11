-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite68_original_real_time_cap_contact_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:36:14.72124+00:00
-- url     : https://prove2.me/submissions/e14dd9d9-de5c-462a-bd31-591c1d38f5d3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_dividend_strategy_predictable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω →
        riskProcess X x D s ω ≤ c)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω) :
    ∀ᵐ ω ∂P,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
          c ≤ riskProcess X x D (Real.toNNReal t) ω} = 0 := by
  classical
  let ν : Measure ℝ := volume.restrict (Ioo (0 : ℝ) (n : ℝ))
  let μ : Measure ℝ≥0 := ν.map Real.toNNReal
  haveI : SFinite ν := inferInstance
  haveI : SFinite μ := inferInstance
  have hOcc := avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
    X hBV x c D hD μ hCap
  have hPredLe : 𝓕.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
    apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      exact (measurableSet_singleton _).prod ((𝓕.le ⊥) A hA)
    · intro i A hA
      exact measurableSet_Ioi.prod ((𝓕.le i) A hA)
  have hDJoint : Measurable (fun z : ℝ≥0 × Ω => D z.1 z.2) :=
    (avram_wave3_04_dividend_strategy_predictable 𝓕 D hD).mono
      hPredLe le_rfl
  have hXJoint : Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2) :=
    chat04_levy_joint_time_state_measurable X
  have hRiskJoint : Measurable
      (fun z : ℝ≥0 × Ω => riskProcess X x D z.1 z.2) := by
    convert (measurable_const.add hXJoint).sub hDJoint using 1 <;> rfl
  filter_upwards [hOcc] with ω hω
  have hRiskTime : Measurable
      (fun s : ℝ≥0 => riskProcess X x D s ω) :=
    hRiskJoint.comp (measurable_id.prodMk measurable_const)
  have hRiskReal : Measurable
      (fun t : ℝ => riskProcess X x D (Real.toNNReal t) ω) :=
    hRiskTime.comp (Measurable.real_toNNReal measurable_id)
  have hBadMeasNN : MeasurableSet {s : ℝ≥0 |
      0 < s ∧ (s : ℝ≥0∞) < ruinTime X x D ω ∧
        c ≤ riskProcess X x D s ω} := by
    have h1 : MeasurableSet {s : ℝ≥0 | 0 < s} :=
      measurableSet_lt measurable_const measurable_id
    have h2 : MeasurableSet {s : ℝ≥0 |
        (s : ℝ≥0∞) < ruinTime X x D ω} :=
      measurableSet_lt measurable_coe_nnreal_ennreal measurable_const
    have h3 : MeasurableSet {s : ℝ≥0 |
        c ≤ riskProcess X x D s ω} :=
      measurableSet_le measurable_const hRiskTime
    have hInter := (h1.inter h2).inter h3
    convert hInter using 1
    ext s
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  have hGoodMeasNN : MeasurableSet {s : ℝ≥0 |
      (0 < s ∧ (s : ℝ≥0∞) < ruinTime X x D ω) →
        riskProcess X x D s ω < c} := by
    convert hBadMeasNN.compl using 1
    ext s
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
    push_neg
    tauto
  have hLift : ∀ᵐ t ∂ν,
      (0 < Real.toNNReal t ∧
          ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω) →
        riskProcess X x D (Real.toNNReal t) ω < c :=
    (MeasureTheory.ae_map_iff
      (Measurable.real_toNNReal measurable_id).aemeasurable
      hGoodMeasNN).mp hω
  have hInside : ∀ᵐ t ∂ν, t ∈ Ioo (0 : ℝ) (n : ℝ) :=
    ae_restrict_mem measurableSet_Ioo
  have hGoodReal : ∀ᵐ t ∂ν,
      ¬(t < (ρ ω : ℝ) ∧
        c ≤ riskProcess X x D (Real.toNNReal t) ω) := by
    filter_upwards [hLift, hInside] with t ht htin
    intro hbad
    have htpos : 0 < t := htin.1
    have htN : (0 : ℝ≥0) < Real.toNNReal t :=
      Real.toNNReal_pos.mpr htpos
    have htρ : Real.toNNReal t < ρ ω := by
      rw [Real.toNNReal_of_nonneg (le_of_lt htpos)]
      exact_mod_cast hbad.1
    have htRuin : ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) <
        ruinTime X x D ω :=
      lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr htρ) (hρruin ω)
    exact not_lt_of_ge hbad.2 (ht ⟨htN, htRuin⟩)
  have hBadMeasReal : MeasurableSet {t : ℝ |
      t < (ρ ω : ℝ) ∧
        c ≤ riskProcess X x D (Real.toNNReal t) ω} :=
    (measurableSet_lt measurable_id measurable_const).inter
      (measurableSet_le measurable_const hRiskReal)
  have hNull : ν {t : ℝ | t < (ρ ω : ℝ) ∧
      c ≤ riskProcess X x D (Real.toNNReal t) ω} = 0 := by
    rw [ae_iff] at hGoodReal
    simpa using hGoodReal
  have hEq : (Ioo (0 : ℝ) (n : ℝ) ∩
      {t : ℝ | t < (ρ ω : ℝ) ∧
        c ≤ riskProcess X x D (Real.toNNReal t) ω}) =
      {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧
        t < (ρ ω : ℝ) ∧
        c ≤ riskProcess X x D (Real.toNNReal t) ω} := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_setOf_eq]
    tauto
  change volume.restrict (Ioo (0 : ℝ) (n : ℝ))
    {t : ℝ | t < (ρ ω : ℝ) ∧
      c ≤ riskProcess X x D (Real.toNNReal t) ω} = 0 at hNull
  rw [Measure.restrict_apply hBadMeasReal] at hNull
  rw [Set.inter_comm, hEq] at hNull
  exact hNull
