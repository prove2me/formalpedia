-- Prove2me | solution 1 for CountingLLL.ContractedWalk.weighted_increases_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:58:25.078596+00:00
-- url     : https://prove2.me/submissions/dea3564f-2ae1-4cf2-b0d7-c9dddfaef440

import Definitions.Def_CountingLLL_ContractedCost
import Definitions.Def_CountingLLL_ContractedGF
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal BigOperators

private theorem weighted_increases_partial (ω : Tape) (i j t : ℕ) :
    (∑ k ∈ Finset.range t, changeWeight ω i j k * (if ω k then 1 else 0)) =
      ∑ k ∈ Finset.range (upwardBefore ω i t), (((j+k : ℕ) : ℝ≥0∞)⁻¹) := by
  classical
  induction t with
  | zero => simp [upwardBefore]
  | succ t ih =>
    have hu : upwardBefore ω i (t+1) = upwardBefore ω i t +
        (if level ω i t ≠ 0 ∧ ω t = true then 1 else 0) := by
      exact Finset.sum_range_succ (fun k => if level ω i k ≠ 0 ∧ ω k = true then 1 else 0) t
    rw [Finset.sum_range_succ, ih, hu]
    by_cases hz : level ω i t = 0
    · simp [hz, changeWeight]
    · cases hb : ω t with
      | false => simp [hz, hb, changeWeight]
      | true => simp [hz, hb, changeWeight, Finset.sum_range_succ]


theorem solution (ω : Tape) (i j : ℕ)
    (h : ∃ t, level ω i t = 0) :
    weightedIncreases ω i j = ∑ k ∈ Finset.range (upwardCount ω i), (((j+k : ℕ) : ℝ≥0∞)⁻¹) := by
  classical
  have hs : stopTime ω i = Nat.find h := by simp [stopTime, h]
  have hz : level ω i (stopTime ω i) = 0 := by rw [hs]; exact Nat.find_spec h
  have hpost (m : ℕ) : level ω i (stopTime ω i + m) = 0 := by
    induction m with
    | zero => simpa using hz
    | succ m ih => simpa [Nat.add_succ, level, ih]
  have hterm (t : ℕ) (ht : stopTime ω i ≤ t) :
      changeWeight ω i j t * (if ω t then 1 else 0) = 0 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ht
    simp [changeWeight, hpost]
  unfold weightedIncreases
  rw [tsum_eq_sum (s := Finset.range (stopTime ω i))]
  · rw [weighted_increases_partial]
    rfl
  · intro t ht
    exact hterm t (by simpa using ht)
