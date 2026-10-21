-- Prove2me | solution 1 for AvramDividend.Classical.finite_ennreal_mass_bin_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T08:42:16.97902+00:00
-- url     : https://prove2.me/submissions/0f486752-85ba-48ea-8430-c1eee70ee279

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Nat.Find

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (m : ℝ≥0∞) (hm : m < ⊤) :
    ∃ n : ℕ, m ≤ (n + 1 : ℝ≥0∞) ∧
      (n = 0 ∨ (n : ℝ≥0∞) < m) := by
  classical
  obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt (ne_of_lt hm)
  have hex : ∃ n : ℕ, m ≤ (n + 1 : ℝ≥0∞) := by
    refine ⟨k, ?_⟩
    exact le_trans (le_of_lt hk) (by exact_mod_cast Nat.le_succ k)
  let n := Nat.find hex
  have hle : m ≤ (n + 1 : ℝ≥0∞) := Nat.find_spec hex
  refine ⟨n, hle, ?_⟩
  by_cases hn : n = 0
  · exact Or.inl hn
  · right
    by_contra hnot
    have hmass : m ≤ (n : ℝ≥0∞) := le_of_not_gt hnot
    have hpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hprev : n - 1 < n := Nat.sub_one_lt hn
    have hmin := Nat.find_min hex hprev
    have hcast := congrArg (fun j : ℕ => (j : ℝ≥0∞))
      (Nat.sub_add_cancel hpos)
    have heq : ((n - 1 : ℕ) : ℝ≥0∞) + 1 = (n : ℝ≥0∞) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hcast
    apply hmin
    simpa only [heq] using hmass
