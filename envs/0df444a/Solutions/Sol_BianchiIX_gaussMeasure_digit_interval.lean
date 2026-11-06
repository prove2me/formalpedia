-- Prove2me | solution 1 for BianchiIX.gaussMeasure_digit_interval
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:25:52.199515+00:00
-- url     : https://prove2.me/submissions/9a263247-869a-4444-bdf3-cad2a18c6707

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
    gaussMeasure (Ioo (1 / ((k : ℝ) + 1)) (1 / (k : ℝ))) =
      ENNReal.ofReal (Real.log (((k : ℝ) + 1) ^ 2 / ((k : ℝ) * ((k : ℝ) + 2))) / Real.log 2) := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.pos
  have hkpos : (0 : ℝ) < k := by linarith
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by linarith
  rw [gaussMeasure_Ioo (by positivity)
    ((div_le_div_iff₀ hk1 hkpos).mpr (by linarith)) ((div_le_one hkpos).mpr hk)]
  rw [← Real.log_div (by positivity : (1 : ℝ) + 1 / (k : ℝ) ≠ 0)
    (by positivity : (1 : ℝ) + 1 / ((k : ℝ) + 1) ≠ 0)]
  congr 3
  field_simp
  ring
