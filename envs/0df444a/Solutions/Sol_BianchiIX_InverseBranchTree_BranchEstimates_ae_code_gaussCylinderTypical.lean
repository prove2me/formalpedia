-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.BranchEstimates.ae_code_gaussCylinderTypical
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:57:51.171194+00:00
-- url     : https://prove2.me/submissions/0fa4b47e-28aa-4d11-b584-0b28dcb425a4

import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_Statistics_BranchTree
import Definitions.Def_BianchiIX_Statistics_TreeCoding
import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_ae_code_property_on_unit
import Theorems.Thm_BianchiIX_ae_volume_gaussCylinderTypicalSet
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
open InverseBranchTree.BranchEstimates


theorem solution {T : InverseBranchTree} {d e : ℕ → ℝ}
    (E : T.BranchEstimates d e) (hB : Literature.BirkhoffErgodicInput ℝ) {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L) :
    ∀ᵐ x ∂(volume.comap (Subtype.val : T.survivors → ℝ)), T.code x ∈ gaussCylinderTypicalSet :=
  E.ae_code_property_on_unit hbudget (ae_volume_gaussCylinderTypicalSet hB)
