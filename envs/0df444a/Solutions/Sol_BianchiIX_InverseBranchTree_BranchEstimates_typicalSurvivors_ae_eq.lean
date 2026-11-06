-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.BranchEstimates.typicalSurvivors_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:12:04.962195+00:00
-- url     : https://prove2.me/submissions/c23a4d65-2b3e-4581-8465-edb055fe790f

import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Definitions.Def_BianchiIX_Statistics_EraBudget
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_ae_code_gaussCylinderTypical
import Theorems.Thm_BianchiIX_InverseBranchTree_mem_typicalSurvivors
import Theorems.Thm_BianchiIX_InverseBranchTree_survivors_measurable
import Theorems.Thm_BianchiIX_InverseBranchTree_typicalSurvivors_subset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.List.Induction
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
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX.InverseBranchTree
open BianchiIX.InverseBranchTree.BranchEstimates


theorem solution {T : InverseBranchTree} {d e : ℕ → ℝ}
    (E : T.BranchEstimates d e) (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L) :
    T.typicalSurvivors =ᵐ[volume] T.survivors := by
  have H : ∀ᵐ x ∂volume.restrict T.survivors, x ∈ T.typicalSurvivors := by
    apply (ae_restrict_iff_subtype T.survivors_measurable).mpr
    filter_upwards [E.ae_code_gaussCylinderTypical hBirkhoff hbudget] with x hx
    exact (T.mem_typicalSurvivors x).mpr hx
  have H' := (ae_restrict_iff' T.survivors_measurable).mp H
  filter_upwards [H'] with x hx
  exact propext ⟨fun h => T.typicalSurvivors_subset h, hx⟩
