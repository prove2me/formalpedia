-- Prove2me | solution 1 for AvramDividend.Classical.avram_mixed_source13_finite_grid_factorial_collision_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:48:37.140191+00:00
-- url     : https://prove2.me/submissions/17402120-1dd8-48cf-82ba-1978702ea451

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_finite_grid_factorial_telescoping_real
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open BigOperators AvramDividend.Classical
noncomputable section
/-- Deterministic monotonicity of the original annulus factorial diagonal. -/
theorem solution
    (k : ℕ) (a b : ℕ → ℕ) (hab : ∀ i, a i ≤ b i) :
    let A : ℕ → ℝ := fun i => a i
    let C : ℕ → ℝ := fun i => b i
    let S : ℝ := ∑ i ∈ Finset.range k, A i
    let H : ℝ := 2 * (∑ i ∈ Finset.range k,
      (∑ j ∈ Finset.range i, A j) * A i)
    H ≤ S * (S - 1) ∧
      S * (S - 1) ≤ H + (∑ i ∈ Finset.range k, C i * (C i - 1)) := by
  classical
  let A : ℕ → ℝ := fun i => a i
  let C : ℕ → ℝ := fun i => b i
  let S : ℝ := ∑ i ∈ Finset.range k, A i
  let H : ℝ := 2 * (∑ i ∈ Finset.range k,
    (∑ j ∈ Finset.range i, A j) * A i)
  change H ≤ S * (S - 1) ∧
    S * (S - 1) ≤ H + (∑ i ∈ Finset.range k, C i * (C i - 1))
  have hA (i : ℕ) : 0 ≤ A i * (A i - 1) := by
    by_cases ha0 : a i = 0
    · simp [A, ha0]
    · have ha1N : 1 ≤ a i := by omega
      have ha1 : (1 : ℝ) ≤ A i := by
        dsimp [A]
        exact_mod_cast ha1N
      have ha0r : 0 ≤ A i := by
        dsimp [A]
        exact Nat.cast_nonneg _
      exact mul_nonneg ha0r (sub_nonneg.mpr ha1)
  have hAC (i : ℕ) : A i * (A i - 1) ≤ C i * (C i - 1) := by
    by_cases hb0 : b i = 0
    · have habi := hab i
      have ha0 : a i = 0 := by omega
      simp [A, C, hb0, ha0]
    · have hb1N : 1 ≤ b i := by omega
      have hb1 : (1 : ℝ) ≤ C i := by
        dsimp [C]
        exact_mod_cast hb1N
      have ha0 : 0 ≤ A i := by
        dsimp [A]
        exact Nat.cast_nonneg _
      have hac : A i ≤ C i := by
        dsimp [A, C]
        exact_mod_cast hab i
      have hprod : 0 ≤ (C i - A i) * (C i + A i - 1) :=
        mul_nonneg (sub_nonneg.mpr hac) (by linarith)
      nlinarith
  have hD0 : 0 ≤ ∑ i ∈ Finset.range k, A i * (A i - 1) :=
    Finset.sum_nonneg (fun i _ => hA i)
  have hDle : (∑ i ∈ Finset.range k, A i * (A i - 1)) ≤
      ∑ i ∈ Finset.range k, C i * (C i - 1) :=
    Finset.sum_le_sum (fun i _ => hAC i)
  have htel := avram_mixed_source13_finite_grid_factorial_telescoping_real k A
  change S * (S - 1) =
    (∑ i ∈ Finset.range k, A i * (A i - 1)) + H at htel
  constructor <;> linarith
