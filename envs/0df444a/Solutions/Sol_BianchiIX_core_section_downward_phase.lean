-- Prove2me | solution 1 for BianchiIX.core_section_downward_phase
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T05:40:06.489946+00:00
-- url     : https://prove2.me/submissions/f1fe4ffd-9936-4564-b410-8fbf3c8f35c5

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

/-- A downward unit-wall crossing of radius at least two is on the negative phase branch. -/
theorem solution {m u w : ℝ}
    (hr : 2 ≤ coreRadius m 1) (hu : 0 ≤ u ∧ u ≤ 1 / 4) (hw : 0 ≤ w ∧ w ≤ 1 / 4)
    (hvel : activeVelocity m u 1 w < 0) : m < 1 := by
  have hcoupling : coupling u 1 w ≤ 5 / 16 := by
    have H := mul_le_mul hu.2 (by linarith only [hw.2] : 1 + w ≤ 5 / 4)
      (by linarith only [hw.1] : 0 ≤ 1 + w) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    dsimp [coupling]
    nlinarith only [H, sq_nonneg u]
  have hs : (2 : ℝ) ^ 2 ≤ coreRadius m 1 ^ 2 :=
    (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg _)).mpr hr
  rw [coreRadius_sq] at hs
  dsimp only [coreEnergy] at hs
  change (m - 1 - coupling u 1 w) * 1 < 0 at hvel
  by_contra! hm
  have hm2 : m ≤ 2 := by linarith only [hvel, hcoupling]
  nlinarith only [hs, mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hm2)]
