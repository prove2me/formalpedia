-- Prove2me | solution 1 for BianchiIX.integrable_gauss_continuous
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:12:17.343966+00:00
-- url     : https://prove2.me/submissions/df02f63a-395c-405c-aa7f-3f65732a95f3

import Definitions.Def_BianchiIX_Statistics_GaussContinuous
import Theorems.Thm_BianchiIX_ae_gaussMeasure_mem_unit
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
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX
noncomputable section
open InverseBranchTree.BranchEstimates


theorem solution {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Integrable f gaussMeasure := by
  have hmem : ∀ᵐ x ∂gaussMeasure, x ∈ Icc (0 : ℝ) 1 :=
    ae_gaussMeasure_mem_unit.mono (fun _ hx => ⟨hx.1.le, hx.2.le⟩)
  have h := hf.integrableOn_Icc (μ := gaussMeasure)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hmem] at h
