-- Prove2me | solution 1 for BianchiIX.gauss_shadowing_of_error_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T13:12:54.876196+00:00
-- url     : https://prove2.me/submissions/e9457e6d-548e-4d8e-ac5e-fa08828c8a84

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Theorems.Thm_BianchiIX_gauss_error_infinite
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


theorem solution {digits : ℕ → ℕ} {y z : ℕ → ℝ}
    (hdigits : ∀ m, 1 ≤ digits m)
    (hy : ∀ m, y m ∈ Set.Icc (0 : ℝ) 1) (hz : ∀ m, z m ∈ Set.Icc (0 : ℝ) 1)
    (hrec : ∀ m, z m = gaussInv (digits m) (z (m + 1)))
    (herror : Tendsto (inverseError digits y) atTop (𝓝 0)) :
    Tendsto (fun m => y m - z m) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp herror (eps * 3 / 16) (by positivity)
  have hsmall : ∀ k ≥ N, inverseError digits y k < eps * 3 / 16 := by
    intro k hk
    apply (le_abs_self _).trans_lt
    simpa only [Real.dist_eq, sub_zero] using hN k hk
  refine ⟨N, fun m hm => ?_⟩
  have hgeom : Summable (fun j : ℕ => (1 / 4 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hbound := (gauss_error_weights_summable hdigits hy m).tsum_le_tsum
    (g := fun j => (1 / 4 : ℝ) ^ j * (eps * 3 / 8))
    (fun j => mul_le_mul_of_nonneg_left (show
      inverseError digits y (m + 2 * j) + inverseError digits y (m + 2 * j + 1) ≤
        eps * 3 / 8 by
          have h0 := hsmall (m + 2 * j) (by omega)
          have h1 := hsmall (m + 2 * j + 1) (by omega)
          linarith) (by positivity : 0 ≤ (1 / 4 : ℝ) ^ j))
    (hgeom.mul_right _)
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at hbound
  have h := gauss_error_infinite hdigits hy hz hrec m
  have hlt : |y m - z m| < eps := by norm_num at hbound; linarith
  simpa only [Real.dist_eq, sub_zero] using hlt
