-- Prove2me | solution 1 for BianchiIX.commonTypicalSet_measurable
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:32:42.411145+00:00
-- url     : https://prove2.me/submissions/a74a99de-7486-4e63-9ac3-8ac8d2217ef6

import Definitions.Def_BianchiIX_Statistics_CommonTypical
import Theorems.Thm_BianchiIX_measurable_birkhoffAverage
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
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace


open Set Filter MeasureTheory
open scoped Topology
open BianchiIX


theorem solution {X ι : Type*} [MeasurableSpace X] [Countable ι]
    {F : X → X} {f : ι → X → ℝ} (l : ι → ℝ)
    (hF : Measurable F) (hf : ∀ i, Measurable (f i)) : MeasurableSet (commonTypicalSet F f l) := by
  simp only [commonTypicalSet, ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_tendsto_fun
    (fun n => measurable_birkhoffAverage hF (hf i) n) measurable_const)
