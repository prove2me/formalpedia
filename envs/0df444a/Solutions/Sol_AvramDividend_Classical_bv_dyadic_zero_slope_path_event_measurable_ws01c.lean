-- Prove2me | solution 1 for AvramDividend.Classical.bv_dyadic_zero_slope_path_event_measurable_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:02:40.540992+00:00
-- url     : https://prove2.me/submissions/0c5e336c-844a-4f9f-aad9-7eafa334acc1

import Mathlib
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem solution
    (d : ℝ) (δ : ℕ → ℝ≥0) :
    MeasurableSet
      {f : ℝ≥0 → ℝ |
        Tendsto (fun n : ℕ =>
          (d * (δ n : ℝ) - f (δ n)) / (δ n : ℝ))
          atTop (𝓝 (0 : ℝ))} := by
  classical
  let v : ℕ → (ℝ≥0 → ℝ) → ℝ :=
    fun n f => (d * (δ n : ℝ) - f (δ n)) / (δ n : ℝ)
  have hv : ∀ n, Measurable (v n) := by
    intro n
    exact (measurable_const.sub (measurable_pi_apply (δ n))).div_const _
  let C : Set (ℝ≥0 → ℝ) :=
    ⋂ k : ℕ, ⋃ N : ℕ, ⋂ n : ℕ,
      {f | N ≤ n → |v n f| ≤ (1 : ℝ) / ((k : ℝ) + 1)}
  have hC : MeasurableSet C := by
    dsimp [C]
    refine MeasurableSet.iInter (fun k => ?_)
    refine MeasurableSet.iUnion (fun N => ?_)
    refine MeasurableSet.iInter (fun n => ?_)
    by_cases hn : N ≤ n
    · simpa [hn] using
        (measurableSet_le ((hv n).abs)
          (measurable_const :
            Measurable (fun _ : ℝ≥0 → ℝ =>
              (1 : ℝ) / ((k : ℝ) + 1))))
    · simp [hn]
  have hIff (f : ℝ≥0 → ℝ) :
      f ∈ C ↔ Tendsto (fun n => v n f) atTop (𝓝 (0 : ℝ)) := by
    simp only [C, Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro h
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      obtain ⟨N, hN⟩ := h k
      refine ⟨N, ?_⟩
      intro n hn
      have hBound := hN n hn
      have hDist : dist (v n f) (0 : ℝ) = |v n f| := by
        simp [Real.dist_eq]
      rw [hDist]
      exact lt_of_le_of_lt hBound hk
    · intro h k
      have hε : 0 < (1 : ℝ) / ((k : ℝ) + 1) := by positivity
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h) _ hε
      refine ⟨N, ?_⟩
      intro n hn
      have hnBound := hN n hn
      have hDist : dist (v n f) (0 : ℝ) = |v n f| := by
        simp [Real.dist_eq]
      rw [hDist] at hnBound
      exact le_of_lt hnBound
  have hEq :
      {f : ℝ≥0 → ℝ |
        Tendsto (fun n => v n f) atTop (𝓝 (0 : ℝ))} = C := by
    ext f
    exact (hIff f).symm
  change MeasurableSet
    {f : ℝ≥0 → ℝ |
      Tendsto (fun n => v n f) atTop (𝓝 (0 : ℝ))}
  rw [hEq]
  exact hC
