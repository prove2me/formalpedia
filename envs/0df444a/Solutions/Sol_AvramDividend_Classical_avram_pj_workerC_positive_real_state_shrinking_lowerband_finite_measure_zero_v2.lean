-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_positive_real_state_shrinking_lowerband_finite_measure_zero_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:21:18.46031+00:00
-- url     : https://prove2.me/submissions/2d64fd73-7ebf-4e05-9d5e-1282f87c95ed

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    [IsFiniteMeasure μ] (Y : α → ℝ) (hYm : Measurable Y) :
    Tendsto (fun k : ℕ =>
      μ {p : α | 0 < Y p ∧ Y p ≤ (1 : ℝ) / ((k : ℝ) + 1)})
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  let S : ℕ → Set α := fun k =>
    {p : α | 0 < Y p ∧ Y p ≤ (1 : ℝ) / ((k : ℝ) + 1)}
  have hMeas : ∀ k, MeasurableSet (S k) := by
    intro k
    exact (measurableSet_lt measurable_const hYm).inter
      (measurableSet_le hYm measurable_const)
  have hAnti : Antitone S := by
    intro i j hij p hp
    refine ⟨hp.1, le_trans hp.2 ?_⟩
    gcongr
  have hEmpty : (⋂ k, S k) = (∅ : Set α) := by
    ext p
    constructor
    · intro hp
      have hP : 0 < Y p := (Set.mem_iInter.mp hp 0).1
      have hAll : ∀ k : ℕ,
          Y p ≤ (1 : ℝ) / ((k : ℝ) + 1) :=
        fun k => (Set.mem_iInter.mp hp k).2
      have hLimit : Y p ≤ 0 :=
        ge_of_tendsto
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
          (Filter.Eventually.of_forall hAll)
      exact False.elim ((not_le_of_gt hP) hLimit)
    · simp
  have hFinite : ∃ k, μ (S k) ≠ ⊤ := by
    exact ⟨0, ne_of_lt (measure_lt_top μ (S 0))⟩
  have hTend :=
    MeasureTheory.tendsto_measure_iInter_atTop
      (fun k => (hMeas k).nullMeasurableSet) hAnti hFinite
  change Tendsto (μ ∘ S) atTop (𝓝 (0 : ℝ≥0∞))
  simpa only [hEmpty, measure_empty] using hTend
