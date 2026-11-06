-- Prove2me | solution 1 for BianchiIX.measurableSet_survivingSet
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:59:29.073507+00:00
-- url     : https://prove2.me/submissions/1b78dbbc-e216-4c0d-a96e-ccc8a9cbed0b

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


theorem solution {X : Type*} [MeasurableSpace X]
    (K : ℕ → Set X) (hK : ∀ m, MeasurableSet (K m)) : MeasurableSet (survivingSet K) :=
  MeasurableSet.iInter hK
