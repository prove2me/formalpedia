-- Prove2me | solution 1 for BianchiIX.hasSum_gaussCylinder_integral
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:19:04.735389+00:00
-- url     : https://prove2.me/submissions/a7715ed0-e7f9-4635-b7cb-b1bd88654e31

import Definitions.Def_BianchiIX_Statistics_GaussContinuous
import Theorems.Thm_BianchiIX_ae_gaussWords_cover
import Theorems.Thm_BianchiIX_gaussWords_disjoint
import Theorems.Thm_BianchiIX_measurableSet_gaussCylinder
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


theorem solution {f : ℝ → ℝ} (hf : Integrable f gaussMeasure) (n : ℕ) :
    HasSum (fun w : GaussWords n => ∫ x in gaussCylinder w.val, f x ∂gaussMeasure)
      (∫ x, f x ∂gaussMeasure) := by
  have h := hasSum_integral_iUnion (fun w : GaussWords n => measurableSet_gaussCylinder w.val)
    (gaussWords_disjoint n) hf.integrableOn
  rwa [Measure.restrict_eq_self_of_ae_mem (ae_gaussWords_cover n)] at h
