-- Prove2me | solution 1 for BianchiIX.coreRadiusReturn_reference_radial_derivative
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:44:35.774539+00:00
-- url     : https://prove2.me/submissions/2f85be42-4ba8-47e5-b9a4-93626790179d

import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Theorems.Thm_BianchiIX_coreRadiusReturn_reference_regular
import Theorems.Thm_BianchiIX_coreRadiusReturn_reference_value
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology


theorem solution {k : ℝ} (hk : 1 < k) :
    fderiv ℝ (coreReturnState coreRadiusReturnTime) ![k, 0, 0] (Pi.single 0 1) = Pi.single 0 1 := by
  have hp : HasDerivAt (fun s : ℝ => (![s, 0, 0] : CoreAngleState)) (Pi.single 0 1) k := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert! hasDerivAt_id k using 1
    · simpa using hasDerivAt_const k (0 : ℝ)
    · simpa using hasDerivAt_const k (0 : ℝ)
  have hF := (coreRadiusReturn_reference_regular hk).2.2.1
  have H := (hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt k hp
  have heq : (fun s : ℝ => coreReturnState coreRadiusReturnTime ![s, 0, 0]) =ᶠ[𝓝 k]
      (fun s => ![s, 0, 0]) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show k ∈ Ioi (1 : ℝ) from hk)] with s hs
    exact coreRadiusReturn_reference_value hs
  exact (H.congr_of_eventuallyEq heq.symm).unique hp
