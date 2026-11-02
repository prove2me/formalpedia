-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:42:41.404832+00:00
-- url     : https://prove2.me/submissions/b239314e-ea90-4312-9f87-e9b87b5940d4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    Measurable[𝓕.rightCont.predictable] a ∧
    (∀ p, |a p| ≤ (1 : ℝ)) ∧
    (∀ p, T < p.1 → a p = 0) := by
  classical
  intro a
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have htime : Measurable (fun p : ℝ≥0 × Ω => p.1) := by
    apply measurable_of_Ioi
    intro t
    have hset : MeasurableSet (Set.Ioi t ×ˢ (Set.univ : Set Ω)) :=
      measurableSet_predictable_Ioi_prod (𝓕 := 𝓕.rightCont)
        (i := t) MeasurableSet.univ
    simpa only [Set.prod_univ] using hset
  have hc : Continuous (fun r : ℝ≥0 => Real.exp (-(q * (r : ℝ)))) := by
    fun_prop
  have hdisc : Measurable (fun p : ℝ≥0 × Ω =>
      Real.exp (-(q * (p.1 : ℝ)))) :=
    hc.measurable.comp htime
  have hset : MeasurableSet {p : ℝ≥0 × Ω | p.1 ≤ T} := by
    simpa only [Set.preimage, Set.mem_Iic] using
      (measurableSet_Iic.preimage htime)
  refine ⟨?_, ?_, ?_⟩
  · exact Measurable.ite hset hdisc measurable_const
  · intro p
    by_cases hp : p.1 ≤ T
    · have hnn : 0 ≤ (p.1 : ℝ) := by positivity
      have hmul : 0 ≤ q * (p.1 : ℝ) := mul_nonneg hq hnn
      have he : Real.exp (-(q * (p.1 : ℝ))) ≤ 1 :=
        (Real.exp_le_one_iff).2 (neg_nonpos.mpr hmul)
      simpa [a, hp, abs_of_pos (Real.exp_pos _)] using he
    · simp [a, hp]
  · intro p hp
    simp [a, not_le.mpr hp]
