-- Prove2me | solution 1 for BianchiIX.gaussWeight_transfer_tsum
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:44:32.49069+00:00
-- url     : https://prove2.me/submissions/c6347647-6697-4411-bf93-a46f64b921d9

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Theorems.Thm_BianchiIX_gaussWeight_transfer_hasSum
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
    (∑' j : ℕ, ENNReal.ofReal
      (gaussWeight (gaussInv ((j : ℝ) + 1) x) * |deriv (gaussInv ((j : ℝ) + 1)) x|)) =
      ENNReal.ofReal (gaussWeight x) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j =>
    mul_nonneg (gaussWeight_pos
      (gaussInv_pos (by linarith [Nat.cast_nonneg (α := ℝ) j]) hx).le).le (abs_nonneg _))
    (gaussWeight_transfer_hasSum hx).summable, (gaussWeight_transfer_hasSum hx).tsum_eq]
