-- Prove2me | solution 1 for BianchiIX.gaussWeight_inverse_jacobian
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:37:13.406795+00:00
-- url     : https://prove2.me/submissions/da8eb3d8-b451-431e-8b9d-7e4db7de8451

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
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

private theorem BianchiIX.hasDerivAt_gaussInv {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) :
    HasDerivAt (gaussInv a) (-1 / (a + x) ^ 2) x := by
  have hden : a + x ≠ 0 := ne_of_gt (by linarith)
  unfold gaussInv
  simpa only [one_div, id_eq] using ((hasDerivAt_id x).const_add a).fun_inv hden

end
end

theorem solution {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) :
    gaussWeight (gaussInv a x) * |deriv (gaussInv a) x| =
      (1 / Real.log 2) * (1 / (a + x) - 1 / (a + 1 + x)) := by
  have hax : 0 < a + x := by linarith
  have hax1 : 0 < a + 1 + x := by linarith
  rw [(hasDerivAt_gaussInv ha hx).deriv]
  simp only [gaussWeight, gaussInv, abs_div, abs_neg, abs_one, abs_pow, abs_of_pos hax]
  field_simp
  ring
