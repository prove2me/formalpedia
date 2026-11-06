-- Prove2me | solution 1 for BianchiIX.integrable_gaussTailObservable
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:36:19.002196+00:00
-- url     : https://prove2.me/submissions/59e49063-7ee0-45fa-840f-25e435d75b47

import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Definitions.Def_BianchiIX_Statistics_GaussDigits
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX
noncomputable section


theorem solution (k : ℕ+) : Integrable (gaussTailObservable k) gaussMeasure :=
  (integrable_const (1 : ℝ)).indicator measurableSet_Ioo
