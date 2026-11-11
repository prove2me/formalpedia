-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_nnreal_dyadic_mesh_data
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T21:59:37.423005+00:00
-- url     : https://prove2.me/submissions/31053568-1858-4363-9c6a-a04ce733d120

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- Exact dyadic deterministic covering meshes for every integer horizon. -/
theorem solution (n : ℕ) :
    ∃ (e : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ) (δ : ℕ → ℝ≥0),
      (∀ k, Monotone (e k)) ∧
      (∀ k, e k 0 = 0) ∧
      (∀ k i, e k (i + 1) ≤ e k i + δ k) ∧
      (∀ k, e k (N k) = (n : ℝ≥0)) ∧
      Tendsto δ atTop (𝓝 0) := by
  refine ⟨(fun k i => (i : ℝ≥0) / (2 : ℝ≥0) ^ k),
    (fun k => n * 2 ^ k), (fun k => 1 / (2 : ℝ≥0) ^ k),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro k i j hij
    have hcast : (i : ℝ≥0) ≤ (j : ℝ≥0) := Nat.cast_le.mpr hij
    exact div_le_div_of_nonneg_right hcast (by positivity)
  · intro k
    simp
  · intro k i
    simpa [Nat.cast_add, Nat.cast_one, add_div]
  · intro k
    simp [Nat.cast_mul, Nat.cast_pow]
  · have ht := NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (1 / 2 : ℝ≥0) < 1)
    simpa only [one_div_pow, one_pow] using ht
