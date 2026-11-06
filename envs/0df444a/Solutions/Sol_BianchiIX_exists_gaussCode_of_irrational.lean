-- Prove2me | solution 1 for BianchiIX.exists_gaussCode_of_irrational
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:45:05.394512+00:00
-- url     : https://prove2.me/submissions/acd0c6aa-86e2-4bcd-abd6-8f1144ae9a56

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Theorems.Thm_BianchiIX_exists_gauss_inverse
import Theorems.Thm_BianchiIX_gaussCode_error_bound
import Theorems.Thm_BianchiIX_gaussMap_iterate_mem_irrational_unit
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
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.MeasurePreserving

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX

section
open BianchiIX
noncomputable section
open Filter Set
open scoped Topology

@[simp] private theorem BianchiIX.shiftDigits_zero (a : ℕ → ℕ+) : shiftDigits a 0 = a := by
  funext i
  simp only [shiftDigits, Nat.zero_add]

end
end

theorem solution {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hi : Irrational x) :
    ∃ a : ℕ → ℕ+, gaussCode a = x := by
  have hy (n : ℕ) := (gaussMap_iterate_mem_irrational_unit hx hi n).1
  choose j hj using fun n => exists_gauss_inverse (hy n)
  let a : ℕ → ℕ+ := fun n => ⟨j n + 1, Nat.succ_pos _⟩
  have herr (n : ℕ) : inverseError (fun k => (a k : ℕ)) (fun k => gaussMap^[k] x) n = 0 := by
    change |gaussMap^[n] x - gaussInv ((j n + 1 : ℕ) : ℝ) (gaussMap^[n + 1] x)| = 0
    rw [Nat.cast_add, Nat.cast_one, Function.iterate_succ_apply', hj n, sub_self, abs_zero]
  have h := gaussCode_error_bound a (fun n => ⟨(hy n).1.le, (hy n).2.le⟩) 0
  simp only [herr, zero_add, add_zero, mul_zero, tsum_zero, shiftDigits_zero,
    Function.iterate_zero, id_eq] at h
  exact ⟨a, (sub_eq_zero.mp (abs_nonpos_iff.mp h)).symm⟩
