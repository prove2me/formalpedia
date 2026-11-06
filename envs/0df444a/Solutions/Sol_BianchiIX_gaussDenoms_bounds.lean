-- Prove2me | solution 1 for BianchiIX.gaussDenoms_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:18:38.252234+00:00
-- url     : https://prove2.me/submissions/d63c1314-c8e3-4004-bc74-0a98e870951d

import Definitions.Def_BianchiIX_Statistics_GaussDistortion
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


theorem solution (a : ℕ → ℕ+) (n : ℕ) :
    1 ≤ (gaussDenoms a n).1 ∧ 0 ≤ (gaussDenoms a n).2 ∧
      (gaussDenoms a n).2 ≤ (gaussDenoms a n).1 := by
  induction n with
  | zero => norm_num [gaussDenoms]
  | succ n ih =>
    have ha : (1 : ℝ) ≤ a n := by exact_mod_cast Nat.succ_le_of_lt (a n).pos
    have hmul : (gaussDenoms a n).1 ≤ (a n : ℝ) * (gaussDenoms a n).1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ (gaussDenoms a n).1 by linarith [ih.1])]
    simp only [gaussDenoms]
    exact ⟨by linarith [ih.1, ih.2.1], by linarith [ih.1], by linarith [ih.2.1]⟩
