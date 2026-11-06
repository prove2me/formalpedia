-- Prove2me | solution 1 for BianchiIX.gaussMap_irrational
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:38:36.073174+00:00
-- url     : https://prove2.me/submissions/b282033f-1e0f-4847-a9e5-3c51e0a4218d

import Definitions.Def_BianchiIX_Statistics_GaussCoding
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

open Set MeasureTheory
open scoped ENNReal
open BianchiIX


theorem solution {x : ℝ} (hx : Irrational x) : Irrational (gaussMap x) := by
  simpa only [gaussMap, Int.fract, one_div] using hx.inv.sub_intCast ⌊1 / x⌋
