-- Prove2me | solution 1 for BianchiIX.gaussMeasure_tail_interval
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:25:36.725939+00:00
-- url     : https://prove2.me/submissions/c3c17210-29b8-4962-a9b8-d2f8587d53ff

import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Theorems.Thm_BianchiIX_gaussMeasure_Ioo
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

open Set MeasureTheory
open scoped ENNReal
open BianchiIX
noncomputable section


theorem solution (k : ℕ+) :
    gaussMeasure (Ioo 0 (1 / (k : ℝ))) = ENNReal.ofReal (Real.log (1 + 1 / (k : ℝ)) / Real.log 2) := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.pos
  have hkpos : (0 : ℝ) < k := by linarith
  simpa using gaussMeasure_Ioo (a := 0) (b := 1 / k) le_rfl (by positivity)
    ((div_le_one hkpos).mpr hk)
