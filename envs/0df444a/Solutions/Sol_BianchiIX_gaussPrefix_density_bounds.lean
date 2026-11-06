-- Prove2me | solution 1 for BianchiIX.gaussPrefix_density_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:42:00.729013+00:00
-- url     : https://prove2.me/submissions/501f7d13-67bf-4eba-bfee-dd9bd320dbab

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussDensity
import Theorems.Thm_BianchiIX_abs_deriv_gaussWord_prefix
import Theorems.Thm_BianchiIX_gaussDenoms_bounds
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim

open BianchiIX
noncomputable section
open Set MeasureTheory
open scoped ENNReal


theorem solution (a : ℕ → ℕ+) (n : ℕ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (1 / 2) * gaussPrefixLength a n ≤ |deriv (gaussWord (digitPrefix a n)) x| ∧
      |deriv (gaussWord (digitPrefix a n)) x| ≤ 2 * gaussPrefixLength a n := by
  let q := (gaussDenoms a n).1
  let p := (gaussDenoms a n).2
  let D := q + p * x
  have h := gaussDenoms_bounds a n
  have hq : 0 < q := by dsimp [q]; linarith [h.1]
  have hp : 0 ≤ p := h.2.1
  have hpq : p ≤ q := h.2.2
  have hDlo : q ≤ D := by dsimp [D]; nlinarith [mul_nonneg hp hx.1]
  have hDhi : D ≤ q + p := by dsimp [D]; nlinarith [mul_nonneg hp (sub_nonneg.mpr hx.2)]
  have hDpos : 0 < D := hq.trans_le hDlo
  have hQpos : 0 < q * (q + p) := by positivity
  have hupper : q * (q + p) ≤ 2 * D ^ 2 := by
    have hs := mul_nonneg (sub_nonneg.mpr hDlo) (show 0 ≤ D + q by positivity)
    nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hpq)]
  have hlower : D ^ 2 ≤ 2 * (q * (q + p)) := by
    have hs := mul_nonneg (sub_nonneg.mpr hDhi) (show 0 ≤ q + p + D by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (show 0 ≤ q + p by positivity)]
  have hu : 1 / D ^ 2 ≤ 2 / (q * (q + p)) :=
    (div_le_div_iff₀ (sq_pos_of_pos hDpos) hQpos).mpr (by simpa using hupper)
  have hl : 1 / (q * (q + p)) ≤ 2 / D ^ 2 :=
    (div_le_div_iff₀ hQpos (sq_pos_of_pos hDpos)).mpr (by simpa using hlower)
  rw [abs_deriv_gaussWord_prefix a n hx.1]
  change (1 / 2) * (1 / (q * (q + p))) ≤ 1 / D ^ 2 ∧
    1 / D ^ 2 ≤ 2 * (1 / (q * (q + p)))
  simp only [div_eq_mul_inv, one_mul] at hl hu ⊢
  constructor <;> linarith
