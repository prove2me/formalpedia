-- Prove2me | solution 1 for BianchiIX.gaussCode_prefix
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T14:44:25.192805+00:00
-- url     : https://prove2.me/submissions/721ee51b-6670-4363-bedc-efea74b050e5

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Theorems.Thm_BianchiIX_gaussCode_recurrence
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

open BianchiIX
noncomputable section
open Filter Set
open scoped Topology

@[simp] private theorem BianchiIX.shiftDigits_zero (a : ℕ → ℕ+) : shiftDigits a 0 = a := by
  funext i
  simp only [shiftDigits, Nat.zero_add]

private theorem BianchiIX.shiftDigits_add (a : ℕ → ℕ+) (m n : ℕ) :
    shiftDigits (shiftDigits a m) n = shiftDigits a (m + n) := by
  funext i
  simp only [shiftDigits, Nat.add_assoc]

private theorem BianchiIX.digitPrefix_succ (a : ℕ → ℕ+) (n : ℕ) :
    digitPrefix a (n + 1) = (a 0 : ℕ) :: digitPrefix (shiftDigits a 1) n := by
  simp [digitPrefix, List.range_succ_eq_map, List.map_map, Function.comp_def, shiftDigits,
    Nat.add_comm]

theorem solution (a : ℕ → ℕ+) (n : ℕ) :
    gaussCode a = gaussWord (digitPrefix a n) (gaussCode (shiftDigits a n)) := by
  induction n generalizing a with
  | zero => simp [digitPrefix, gaussWord]
  | succ n ih =>
    rw [gaussCode_recurrence a, digitPrefix_succ]
    simpa only [gaussWord, shiftDigits_add, Nat.one_add] using
      congrArg (gaussInv (a 0)) (ih (shiftDigits a 1))
