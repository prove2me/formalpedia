-- Prove2me | solution 1 for BianchiIX.gaussMap_iterate_code
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T14:45:24.424572+00:00
-- url     : https://prove2.me/submissions/304b1bb4-2215-41e9-8faf-40ad5b178e2c

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

section
open BianchiIX
noncomputable section
open Filter
open scoped Topology

private theorem BianchiIX.gaussInv_pos {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) : 0 < gaussInv a x := by
  unfold gaussInv
  exact one_div_pos.mpr (by linarith)

end
end

@[simp] private theorem BianchiIX.shiftDigits_zero (a : ℕ → ℕ+) : shiftDigits a 0 = a := by
  funext i
  simp only [shiftDigits, Nat.zero_add]

private theorem BianchiIX.shiftDigits_add (a : ℕ → ℕ+) (m n : ℕ) :
    shiftDigits (shiftDigits a m) n = shiftDigits a (m + n) := by
  funext i
  simp only [shiftDigits, Nat.add_assoc]

private theorem BianchiIX.gaussCode_tendsto (a : ℕ → ℕ+) : Tendsto (gaussApprox a) atTop (𝓝 (gaussCode a)) :=
  (cauchySeq_tendsto_of_complete (gaussApprox_cauchy a)).choose_spec

private theorem BianchiIX.gaussCode_mem_unit (a : ℕ → ℕ+) : gaussCode a ∈ Icc (0 : ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (gaussCode_tendsto a) (Eventually.of_forall (gaussApprox_mem_unit a))

private theorem BianchiIX.gaussCode_pos (a : ℕ → ℕ+) : 0 < gaussCode a := by
  rw [gaussCode_recurrence a]
  apply gaussInv_pos _ (gaussCode_mem_unit (shiftDigits a 1)).1
  exact_mod_cast Nat.succ_le_of_lt (a 0).pos

private theorem BianchiIX.gaussCode_lt_one (a : ℕ → ℕ+) : gaussCode a < 1 := by
  rw [gaussCode_recurrence a]
  have ha : (1 : ℝ) ≤ a 0 := by exact_mod_cast Nat.succ_le_of_lt (a 0).pos
  have ht := gaussCode_pos (shiftDigits a 1)
  unfold gaussInv
  exact (div_lt_one (by positivity)).mpr (by linarith)

private theorem BianchiIX.gaussCode_reciprocal (a : ℕ → ℕ+) :
    1 / gaussCode a = (a 0 : ℝ) + gaussCode (shiftDigits a 1) := by
  rw [gaussCode_recurrence a]
  simp only [gaussInv, one_div_one_div]

private theorem BianchiIX.gaussCode_digit (a : ℕ → ℕ+) : ⌊1 / gaussCode a⌋ = (a 0 : ℤ) := by
  apply Int.floor_eq_iff.mpr
  rw [gaussCode_reciprocal]
  change ((a 0 : ℕ) : ℝ) ≤ ((a 0 : ℕ) : ℝ) + gaussCode (shiftDigits a 1) ∧
    ((a 0 : ℕ) : ℝ) + gaussCode (shiftDigits a 1) < ((a 0 : ℕ) : ℝ) + 1
  exact ⟨by linarith [gaussCode_pos (shiftDigits a 1)],
    by linarith [gaussCode_lt_one (shiftDigits a 1)]⟩

private theorem BianchiIX.gaussMap_code (a : ℕ → ℕ+) : gaussMap (gaussCode a) = gaussCode (shiftDigits a 1) := by
  unfold gaussMap Int.fract
  rw [gaussCode_digit, gaussCode_reciprocal]
  push_cast
  ring

theorem solution (a : ℕ → ℕ+) (n : ℕ) :
    gaussMap^[n] (gaussCode a) = gaussCode (shiftDigits a n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, gaussMap_code, shiftDigits_add]
