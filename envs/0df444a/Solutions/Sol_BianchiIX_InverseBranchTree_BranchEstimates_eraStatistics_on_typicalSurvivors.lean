-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.BranchEstimates.eraStatistics_on_typicalSurvivors
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:14:02.222614+00:00
-- url     : https://prove2.me/submissions/a39439cd-e5c2-48f9-afc3-955247c40777

import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Definitions.Def_BianchiIX_Statistics_TreeOrbits
import Definitions.Def_BianchiIX_Statistics_EraStatistics
import Definitions.Def_BianchiIX_Statistics_EraBudget
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_phase_error_le
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_phase_mem_unit
import Theorems.Thm_BianchiIX_InverseBranchTree_mem_typicalSurvivors
import Theorems.Thm_BianchiIX_eraStatistics_of_typical_code
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
    (E : T.BranchEstimates d e) (hd : Tendsto d atTop (𝓝 0))
    (x : T.survivors) (hx : x.val ∈ T.typicalSurvivors) : EraStatistics (T.digits x) (T.phase x) :=
  eraStatistics_of_typical_code (T.digits x) ((T.mem_typicalSurvivors x).mp hx) (E.phase_mem_unit x)
    (squeeze_zero (fun _ => abs_nonneg _) (E.phase_error_le x) hd)
