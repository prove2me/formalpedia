-- Prove2me | solution 1 for BianchiIX.gaussWeight_transfer_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:42:16.34758+00:00
-- url     : https://prove2.me/submissions/4e841207-1645-4765-a137-61c7c27cd7df

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Theorems.Thm_BianchiIX_gaussWeight_transfer_sum
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

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX

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

theorem solution {x : ℝ} (hx : 0 ≤ x) :
    HasSum (fun j : ℕ =>
      gaussWeight (gaussInv ((j : ℝ) + 1) x) * |deriv (gaussInv ((j : ℝ) + 1)) x|) (gaussWeight x) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun j =>
    mul_nonneg (gaussWeight_pos
      (gaussInv_pos (by linarith [Nat.cast_nonneg (α := ℝ) j]) hx).le).le (abs_nonneg _)) _).mpr
  simp_rw [gaussWeight_transfer_sum hx]
  have hN : Tendsto (fun N : ℕ => (N : ℝ) + (1 + x)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 + x) tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp hN
  have hlim := ((tendsto_const_nhds (x := (1 / (1 + x) : ℝ))).sub hinv).const_mul (1 / Real.log 2)
  simpa only [Function.comp_def, one_div, add_assoc, sub_zero, gaussWeight,
    mul_inv_rev, mul_comm] using hlim
