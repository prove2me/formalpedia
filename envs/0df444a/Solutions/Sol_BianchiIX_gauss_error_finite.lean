-- Prove2me | solution 1 for BianchiIX.gauss_error_finite
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T13:10:02.336936+00:00
-- url     : https://prove2.me/submissions/aa0dfa5f-5328-489e-8fe6-7b13db6a9dc5

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Theorems.Thm_BianchiIX_gaussInv_pair_lipschitz
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open BianchiIX
noncomputable section
open Filter
open scoped Topology

private theorem BianchiIX.gaussInv_pos {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) : 0 < gaussInv a x := by
  unfold gaussInv
  exact one_div_pos.mpr (by linarith)

private theorem BianchiIX.gaussInv_lipschitz {a x y : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |gaussInv a x - gaussInv a y| ≤ |x - y| := by
  have hax : 0 < a + x := by linarith
  have hay : 0 < a + y := by linarith
  have hden : 1 ≤ (a + x) * (a + y) := by
    nlinarith [mul_nonneg (show 0 ≤ a + x - 1 by linarith)
      (show 0 ≤ a + y - 1 by linarith)]
  have hid : gaussInv a x - gaussInv a y = (y - x) / ((a + x) * (a + y)) := by
    unfold gaussInv
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos (mul_pos hax hay), abs_sub_comm y x]
  exact div_le_self (abs_nonneg _) hden

private theorem BianchiIX.gauss_two_step_error {a b y0 y1 y2 z2 : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2) (hz2 : 0 ≤ z2) :
    |y0 - gaussInv a (gaussInv b z2)| ≤
      |y0 - gaussInv a y1| + |y1 - gaussInv b y2| + (1 / 4) * |y2 - z2| := by
  have h1 := abs_sub_le y0 (gaussInv a y1) (gaussInv a (gaussInv b z2))
  have h2 := abs_sub_le (gaussInv a y1) (gaussInv a (gaussInv b y2)) (gaussInv a (gaussInv b z2))
  have hsingle := gaussInv_lipschitz ha hy1 (gaussInv_pos hb hy2).le
  have hpair := gaussInv_pair_lipschitz ha hb hy2 hz2
  linarith

private theorem BianchiIX.gauss_comparison_step {digits : ℕ → ℕ} {y z : ℕ → ℝ}
    (hdigits : ∀ m, 1 ≤ digits m) (hy : ∀ m, 0 ≤ y m) (hz : ∀ m, 0 ≤ z m)
    (hrec : ∀ m, z m = gaussInv (digits m) (z (m + 1))) (m : ℕ) :
    |y m - z m| ≤ inverseError digits y m + inverseError digits y (m + 1) +
      (1 / 4) * |y (m + 2) - z (m + 2)| := by
  have ha : (1 : ℝ) ≤ digits m := by exact_mod_cast hdigits m
  have hb : (1 : ℝ) ≤ digits (m + 1) := by exact_mod_cast hdigits (m + 1)
  have h := gauss_two_step_error (y0 := y m) ha hb (hy (m + 1)) (hy (m + 2)) (hz (m + 2))
  rw [hrec m, hrec (m + 1)]
  simpa only [inverseError, Nat.add_assoc] using h

/-- Finite expansion retains the actual terminal discrepancy. -/
theorem solution {digits : ℕ → ℕ} {y z : ℕ → ℝ}
    (hdigits : ∀ m, 1 ≤ digits m) (hy : ∀ m, 0 ≤ y m) (hz : ∀ m, 0 ≤ z m)
    (hrec : ∀ m, z m = gaussInv (digits m) (z (m + 1))) (m N : ℕ) :
    |y m - z m| ≤
      (∑ j ∈ Finset.range N, (1 / 4 : ℝ) ^ j *
        (inverseError digits y (m + 2 * j) + inverseError digits y (m + 2 * j + 1))) +
      (1 / 4 : ℝ) ^ N * |y (m + 2 * N) - z (m + 2 * N)| := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs := gauss_comparison_step hdigits hy hz hrec (m + 2 * N)
    have hnext : m + 2 * N + 2 = m + 2 * (N + 1) := by ring
    calc
      _ ≤ (∑ j ∈ Finset.range N, (1 / 4 : ℝ) ^ j *
          (inverseError digits y (m + 2 * j) + inverseError digits y (m + 2 * j + 1))) +
          (1 / 4 : ℝ) ^ N * |y (m + 2 * N) - z (m + 2 * N)| := ih
      _ ≤ (∑ j ∈ Finset.range N, (1 / 4 : ℝ) ^ j *
          (inverseError digits y (m + 2 * j) + inverseError digits y (m + 2 * j + 1))) +
          (1 / 4 : ℝ) ^ N * (inverseError digits y (m + 2 * N) +
            inverseError digits y (m + 2 * N + 1) +
            (1 / 4) * |y (m + 2 * N + 2) - z (m + 2 * N + 2)|) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (by positivity :
          0 ≤ (1 / 4 : ℝ) ^ N))
      _ = _ := by rw [Finset.sum_range_succ, pow_succ, hnext]; ring
