-- Prove2me | solution 1 for BianchiIX.exists_restartShearReturn_common_regular
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:59:36.125714+00:00
-- url     : https://prove2.me/submissions/72e5aefc-0bad-4364-9fd7-32a28bc66a75

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_ShearTransportData
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_EraReturnData
import Theorems.Thm_BianchiIX_exists_restartShearReturn_all_active_joint_regular
import Theorems.Thm_BianchiIX_exists_restartShearTail_connection
import Theorems.Thm_BianchiIX_exists_restartShearTail_cutoff_germs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartShearTail_fast_return_regular :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s v.1.1 v.1.2 v.2) ((ζ, ν), ρ) ∧
          ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnState h s v.1.1 v.1.2 v.2) ((ζ, ν), ρ) ∧
          ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s v.1.1 v.1.2 v.2) ((ζ, ν), ρ) ∧
          ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnTime h s v.1.1 v.1.2 v.2) ((ζ, ν), ρ) := by
  obtain ⟨hG, hhG, HG⟩ := exists_restartShearTail_cutoff_germs
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearTail_connection
  refine ⟨min hG hC, lt_min hhG hhC, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aG, haG, HAG⟩ := HG h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aC, haC, HAC⟩ := HC h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq hD hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  refine ⟨min aG aC, lt_min haG haC, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s
  obtain ⟨HP, HG, HX, HT⟩ := HAG a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hcp, hcg, hcx, hct⟩ :=
    HAC a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  exact ⟨hcp.congr_of_eventuallyEq HP, hcg.congr_of_eventuallyEq HG,
    hcx.congr_of_eventuallyEq HX, hct.congr_of_eventuallyEq HT⟩

end
end

/-- Both small-wall orderings use one jointly C2 positive-shear return on the whole radial annulus. -/
theorem solution :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) → (0 < n₂ ∧ n₂ ≤ 2 * ε * a) →
          (0 < n₃ ∧ n₃ ≤ 2 * ε * a) → min n₂ n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s v.1.1 v.1.2 v.2) ((n₂, n₃), ρ) ∧
          ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnState h s v.1.1 v.1.2 v.2) ((n₂, n₃), ρ) ∧
          ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s v.1.1 v.1.2 v.2) ((n₂, n₃), ρ) ∧
          ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnTime h s v.1.1 v.1.2 v.2) ((n₂, n₃), ρ) := by
  obtain ⟨hA, hhA, HA⟩ := exists_restartShearReturn_all_active_joint_regular
  obtain ⟨hT, hhT, HT⟩ := exists_restartShearTail_fast_return_regular
  refine ⟨min hA hT, lt_min hhA hhT, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aA, haA, HAA⟩ := HA h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq (by linarith only [hD, hP])
  obtain ⟨aT, haT, HAT⟩ := HT h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq hD hP
  refine ⟨min aA aT, lt_min haA haT, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ hmin ρ hρ s
  by_cases hn₃ : n₃ ≤ a ^ P
  · exact HAA a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃
      ⟨hε.1, hε.2.trans (by norm_num)⟩ h₂ h₃ hn₃ ρ hρ
  · exact HAT a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε
      ⟨h₂.1, (min_le_iff.mp hmin).resolve_right hn₃, h₂.2⟩ h₃ ρ hρ
