-- Prove2me | solution 1 for BianchiIX.abs_deriv_gaussWord_prefix
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:25:01.95793+00:00
-- url     : https://prove2.me/submissions/49af8a17-764d-43ce-8d7b-a89104fb4b15

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussDistortion
import Theorems.Thm_BianchiIX_gaussDenoms_bounds
import Theorems.Thm_BianchiIX_hasDerivAt_gaussWord_prefix
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

open BianchiIX
noncomputable section
open Set Finset

private theorem BianchiIX.gaussDenom_pos (a : ℕ → ℕ+) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 < gaussDenom a n x := by
  have h := gaussDenoms_bounds a n
  dsimp [gaussDenom]
  nlinarith [mul_nonneg h.2.1 hx]

theorem solution (a : ℕ → ℕ+) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |deriv (gaussWord (digitPrefix a n)) x| = 1 / (gaussDenom a n x) ^ 2 := by
  rw [(hasDerivAt_gaussWord_prefix a n hx).deriv, abs_div, abs_pow, abs_neg,
    abs_one, one_pow, abs_pow, abs_of_pos (gaussDenom_pos a n hx)]
