-- Prove2me | solution 1 for BianchiIX.measurable_birkhoffAverage
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:25:02.60948+00:00
-- url     : https://prove2.me/submissions/7e6bc81b-2ec7-45ac-943f-587e318230e1

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


theorem solution {X : Type*} [MeasurableSpace X] {F : X → X} {f : X → ℝ}
    (hF : Measurable F) (hf : Measurable f) (n : ℕ) :
    Measurable (birkhoffAverage ℝ F f n) := by
  change Measurable (fun x => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f (F^[j] x))
  exact (Finset.measurable_sum _ (fun j _ => hf.comp (hF.iterate j))).const_mul _
