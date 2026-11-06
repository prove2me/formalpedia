-- Prove2me | solution 1 for BianchiIX.gaussCode_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T14:51:19.188633+00:00
-- url     : https://prove2.me/submissions/7c38bdb5-121a-418a-abd8-8658e1ba934a

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Theorems.Thm_BianchiIX_gaussCode_recurrence
import Theorems.Thm_BianchiIX_gauss_error_infinite
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

private theorem BianchiIX.shiftDigits_add (a : ℕ → ℕ+) (m n : ℕ) :
    shiftDigits (shiftDigits a m) n = shiftDigits a (m + n) := by
  funext i
  simp only [shiftDigits, Nat.add_assoc]

private theorem BianchiIX.gaussCode_tendsto (a : ℕ → ℕ+) : Tendsto (gaussApprox a) atTop (𝓝 (gaussCode a)) :=
  (cauchySeq_tendsto_of_complete (gaussApprox_cauchy a)).choose_spec

private theorem BianchiIX.gaussCode_mem_unit (a : ℕ → ℕ+) : gaussCode a ∈ Icc (0 : ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (gaussCode_tendsto a) (Eventually.of_forall (gaussApprox_mem_unit a))

private theorem BianchiIX.gaussCode_shift_recurrence (a : ℕ → ℕ+) (m : ℕ) :
    gaussCode (shiftDigits a m) =
      gaussInv (a m) (gaussCode (shiftDigits a (m + 1))) := by
  simpa only [shiftDigits_add, shiftDigits, Nat.add_zero] using
    gaussCode_recurrence (shiftDigits a m)

/-- The comparison orbit is now the explicitly constructed code of the prescribed digits. -/
theorem solution (a : ℕ → ℕ+) {y : ℕ → ℝ}
    (hy : ∀ m, y m ∈ Icc (0 : ℝ) 1) (m : ℕ) :
    |y m - gaussCode (shiftDigits a m)| ≤ ∑' j : ℕ, (1 / 4 : ℝ) ^ j *
      (inverseError (fun k => (a k : ℕ)) y (m + 2 * j) +
        inverseError (fun k => (a k : ℕ)) y (m + 2 * j + 1)) :=
  gauss_error_infinite (fun k => Nat.succ_le_of_lt (a k).pos) hy
    (fun k => gaussCode_mem_unit (shiftDigits a k)) (gaussCode_shift_recurrence a) m
