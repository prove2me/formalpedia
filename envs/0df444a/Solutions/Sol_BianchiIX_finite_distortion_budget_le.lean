-- Prove2me | solution 1 for BianchiIX.finite_distortion_budget_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:58:22.027257+00:00
-- url     : https://prove2.me/submissions/0933d5aa-44ea-4fdd-9e03-f8da23d42a80

import Definitions.Def_BianchiIX_Statistics_StoppedMass
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


theorem solution (d e : ℕ → ℝ)
    (hd0 : ∀ j, 0 ≤ d j) (he0 : ∀ j, 0 ≤ e j) (hd : Summable d) (he : Summable e) (n : ℕ) :
    (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤
      (∑' j, e j) + 2 * ∑' j, d (j + 1) := by
  let f := fun j => e j + if j = 0 then 0 else 2 * d j
  have hds : Summable (fun j => d (j + 1)) := (summable_nat_add_iff 1).mpr hd
  have hes : Summable (fun j => e (j + 1)) := (summable_nat_add_iff 1).mpr he
  have hfs : Summable (fun j => f (j + 1)) := by
    simpa only [f, Nat.add_one_ne_zero, if_false] using hes.add (hds.mul_left 2)
  have hf : Summable f := (summable_nat_add_iff 1).mp hfs
  have htail : (∑' j, f (j + 1)) = (∑' j, e (j + 1)) + 2 * ∑' j, d (j + 1) := by
    simp only [f, Nat.add_one_ne_zero, if_false]
    rw [hes.tsum_add (hds.mul_left 2), tsum_mul_left]
  have htotal : (∑' j, f j) = (∑' j, e j) + 2 * ∑' j, d (j + 1) := by
    rw [hf.tsum_eq_zero_add, htail, he.tsum_eq_zero_add]
    simp [f, add_assoc]
  rw [← htotal]
  apply hf.sum_le_tsum (Finset.range n)
  intro j _
  dsimp [f]
  split_ifs <;> linarith [hd0 j, he0 j]
