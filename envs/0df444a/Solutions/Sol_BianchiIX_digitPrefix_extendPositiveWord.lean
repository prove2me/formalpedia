-- Prove2me | solution 1 for BianchiIX.digitPrefix_extendPositiveWord
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:38:53.134084+00:00
-- url     : https://prove2.me/submissions/c580f5f3-6947-4950-8ce0-60ff44f1b61e

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_TreeMeasure
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


open Set MeasureTheory
open scoped NNReal ENNReal
open BianchiIX


theorem solution (w : List ℕ+) :
    digitPrefix (extendPositiveWord w) w.length = w.map (fun a : ℕ+ => (a : ℕ)) := by
  apply List.ext_getElem
  · simp [digitPrefix]
  · intro i hi hj
    simp only [digitPrefix, List.length_map, List.length_range] at hi
    simp [digitPrefix, extendPositiveWord, hi]
