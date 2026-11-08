-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_monotone_grid_nonuniform_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:52:17.977494+00:00
-- url     : https://prove2.me/submissions/573718d2-d5fc-443c-838e-34d02c240bed

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original endpoint and monotonicity hypotheses allow a partition
    consisting of a single macroscopic first cell and repeated endpoints. -/
theorem solution
    (T : ℝ) (hT : 0 < T) :
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0 ∧
        ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n, u n 1 = u n (n + 1)) ∧
      ¬ (∀ n i, (u n i : ℝ) =
        T * (i : ℝ) / ((n : ℝ) + 2)) := by
  classical
  have hnonneg (n : ℕ) :
      0 ≤ T - T / ((n : ℝ) + 2) := by
    apply sub_nonneg.mpr
    apply div_le_self (le_of_lt hT)
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  let a : ℕ → ℝ≥0 :=
    fun n => ⟨T - T / ((n : ℝ) + 2), hnonneg n⟩
  let u : ℕ → ℕ → ℝ≥0 :=
    fun n i => if i = 0 then 0 else a n
  have hg : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) =
        T - T / ((n : ℝ) + 2)) := by
    intro n
    constructor
    · simp [u]
    · have hn1 : n + 1 ≠ 0 := Nat.succ_ne_zero n
      simp only [u, if_neg hn1]
      rfl
  have hm : ∀ n i, i < n + 1 →
      u n i ≤ u n (i + 1) := by
    intro n i hi
    by_cases hi0 : i = 0
    · subst i
      simp [u]
    · have hsucc : i + 1 ≠ 0 := Nat.succ_ne_zero i
      simp [u, hi0, hsucc]
  have hl : ∀ n, u n 1 = u n (n + 1) := by
    intro n
    have hn1 : n + 1 ≠ 0 := Nat.succ_ne_zero n
    simp [u, hn1]
  refine ⟨u, hg, hm, hl, ?_⟩
  intro huniform
  have hu11 := huniform 1 1
  have hgrid12 := (hg 1).2
  have heq := congrArg (fun t : ℝ≥0 => (t : ℝ)) (hl 1)
  norm_num at hu11 hgrid12
  nlinarith
