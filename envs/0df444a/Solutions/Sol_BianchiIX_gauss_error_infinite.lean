-- Prove2me | solution 1 for BianchiIX.gauss_error_infinite
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T13:11:58.258202+00:00
-- url     : https://prove2.me/submissions/4671140d-b15a-4198-8174-2e657d8d0d5c

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Theorems.Thm_BianchiIX_gauss_error_finite
import Theorems.Thm_BianchiIX_gauss_error_weights_summable
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

private theorem BianchiIX.gauss_error_finite_bound {digits : ℕ → ℕ} {y z : ℕ → ℝ}
    (hdigits : ∀ m, 1 ≤ digits m)
    (hy : ∀ m, y m ∈ Set.Icc (0 : ℝ) 1) (hz : ∀ m, z m ∈ Set.Icc (0 : ℝ) 1)
    (hrec : ∀ m, z m = gaussInv (digits m) (z (m + 1))) (m N : ℕ) :
    |y m - z m| ≤
      (∑ j ∈ Finset.range N, (1 / 4 : ℝ) ^ j *
        (inverseError digits y (m + 2 * j) + inverseError digits y (m + 2 * j + 1))) +
      (1 / 4 : ℝ) ^ N := by
  have htail : |y (m + 2 * N) - z (m + 2 * N)| ≤ 1 :=
    abs_le.mpr ⟨by linarith [(hy (m + 2 * N)).1, (hz (m + 2 * N)).2],
      by linarith [(hz (m + 2 * N)).1, (hy (m + 2 * N)).2]⟩
  have h := gauss_error_finite hdigits (fun n => (hy n).1) (fun n => (hz n).1) hrec m N
  have htail' := mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ (1 / 4 : ℝ) ^ N)
  linarith

/-- Equation (3.10), with the exact comparison sequence specified by its recurrence. -/
theorem solution {digits : ℕ → ℕ} {y z : ℕ → ℝ}
    (hdigits : ∀ m, 1 ≤ digits m)
    (hy : ∀ m, y m ∈ Set.Icc (0 : ℝ) 1) (hz : ∀ m, z m ∈ Set.Icc (0 : ℝ) 1)
    (hrec : ∀ m, z m = gaussInv (digits m) (z (m + 1))) (m : ℕ) :
    |y m - z m| ≤ ∑' j : ℕ, (1 / 4 : ℝ) ^ j *
      (inverseError digits y (m + 2 * j) + inverseError digits y (m + 2 * j + 1)) := by
  have hsum := (gauss_error_weights_summable hdigits hy m).hasSum.tendsto_sum_nat
  have hpow : Tendsto (fun N : ℕ => (1 / 4 : ℝ) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := ge_of_tendsto' (hsum.add hpow) (gauss_error_finite_bound hdigits hy hz hrec m)
  simpa only [add_zero] using h
