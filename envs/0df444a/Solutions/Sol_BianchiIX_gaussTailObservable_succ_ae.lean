-- Prove2me | solution 1 for BianchiIX.gaussTailObservable_succ_ae
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:45:02.688148+00:00
-- url     : https://prove2.me/submissions/6e90ae41-0866-4597-8167-d87768192cf3

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Definitions.Def_BianchiIX_Statistics_GaussDigits
import Theorems.Thm_BianchiIX_ae_gaussMeasure_irrational
import Theorems.Thm_BianchiIX_ae_gaussMeasure_mem_unit
import Theorems.Thm_BianchiIX_exists_gaussCode_of_irrational
import Theorems.Thm_BianchiIX_gaussTailObservable_succ_code
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


theorem solution (k : ℕ+) :
    gaussTailObservable (k + 1) =ᵐ[gaussMeasure]
      (fun x => gaussTailObservable k x - gaussCylinderObservable [(k : ℕ)] x) := by
  filter_upwards [ae_gaussMeasure_mem_unit, ae_gaussMeasure_irrational] with x hx hi
  obtain ⟨a, rfl⟩ := exists_gaussCode_of_irrational hx hi
  exact gaussTailObservable_succ_code a k
