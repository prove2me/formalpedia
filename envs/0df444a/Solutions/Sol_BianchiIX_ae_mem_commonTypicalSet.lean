-- Prove2me | solution 1 for BianchiIX.ae_mem_commonTypicalSet
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:26:08.43683+00:00
-- url     : https://prove2.me/submissions/61ab60b2-72d5-4980-8516-92f9c753f4a8

import Definitions.Def_BianchiIX_Statistics_CommonTypical
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
    (μ : Measure X) (F : X → X) (f : ι → X → ℝ) (l : ι → ℝ)
    (h : ∀ i, ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ F (f i) n x) atTop (𝓝 (l i))) :
    ∀ᵐ x ∂μ, x ∈ commonTypicalSet F f l := by
  exact ae_all_iff.mpr h
