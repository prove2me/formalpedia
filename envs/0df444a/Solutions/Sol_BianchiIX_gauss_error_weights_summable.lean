-- Prove2me | solution 1 for BianchiIX.gauss_error_weights_summable
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T13:07:18.665497+00:00
-- url     : https://prove2.me/submissions/c23f661c-eb59-429a-837d-4ca63ecf3433

import Definitions.Def_BianchiIX_Statistics_GaussInverse
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

private theorem BianchiIX.gaussInv_le_one {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) : gaussInv a x ≤ 1 := by
  unfold gaussInv
  exact (div_le_one (by linarith : 0 < a + x)).mpr (by linarith)

private theorem BianchiIX.inverseError_le_one {digits : ℕ → ℕ} {y : ℕ → ℝ}
    (hdigits : ∀ m, 1 ≤ digits m) (hy : ∀ m, y m ∈ Set.Icc (0 : ℝ) 1) (m : ℕ) :
    inverseError digits y m ≤ 1 := by
  have ha : (1 : ℝ) ≤ digits m := by exact_mod_cast hdigits m
  have hpos := gaussInv_pos ha (hy (m + 1)).1
  have hle := gaussInv_le_one ha (hy (m + 1)).1
  exact abs_le.mpr ⟨by linarith [(hy m).1], by linarith [(hy m).2]⟩

theorem solution {digits : ℕ → ℕ} {y : ℕ → ℝ}
    (hdigits : ∀ m, 1 ≤ digits m) (hy : ∀ m, y m ∈ Set.Icc (0 : ℝ) 1) (m : ℕ) :
    Summable (fun j => (1 / 4 : ℝ) ^ j *
      (inverseError digits y (m + 2 * j) + inverseError digits y (m + 2 * j + 1))) := by
  have hgeom : Summable (fun j : ℕ => (1 / 4 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  apply Summable.of_nonneg_of_le _ _ (hgeom.mul_right 2)
  · intro j
    unfold inverseError
    positivity
  · intro j
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (1 / 4 : ℝ) ^ j)
    have h0 := inverseError_le_one hdigits hy (m + 2 * j)
    have h1 := inverseError_le_one hdigits hy (m + 2 * j + 1)
    linarith
