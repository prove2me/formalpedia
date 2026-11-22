-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_deterministic_horizon_discount_predictable_unit_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T11:30:55.466239+00:00
-- url     : https://prove2.me/submissions/8885acc6-bc61-4af5-8a0f-a0751e31a993

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_predictable_time_exponential_discount_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    let a : ℝ≥0 × Ω → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    Measurable[𝓕.rightCont.predictable] a ∧
      ∀ p, 0 ≤ a p ∧ a p ≤ 1 := by
  have hExp : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ)))) :=
    avram_wave7_07_original_predictable_time_exponential_discount_measurable
      (𝓕 := 𝓕) q
  have hHorizon : MeasurableSet[𝓕.rightCont.predictable]
      {p : ℝ≥0 × Ω | p.1 ≤ T} := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    have hEmbed : Measurable (fun p : ℝ≥0 × Ω => (p, (0 : ℝ))) :=
      measurable_id.prodMk measurable_const
    convert
      (avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable
        𝓕 T).preimage hEmbed using 1
    ext p
    rfl
  refine ⟨hExp.ite hHorizon measurable_const, ?_⟩
  intro p
  dsimp
  split_ifs with hp
  · constructor
    · exact (Real.exp_pos _).le
    · apply Real.exp_le_one_iff.mpr
      have ht : 0 ≤ (p.1 : ℝ) := by positivity
      nlinarith [mul_nonneg hq ht]
  · norm_num

