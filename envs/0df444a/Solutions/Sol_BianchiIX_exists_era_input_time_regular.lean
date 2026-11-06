-- Prove2me | solution 1 for BianchiIX.exists_era_input_time_regular
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:37:37.499203+00:00
-- url     : https://prove2.me/submissions/e3b7274a-59af-4ab5-a875-33723259fc3a

import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_EraReturnData
import Theorems.Thm_BianchiIX_exists_era_time_regular
import Theorems.Thm_BianchiIX_exists_retained_era_parameter_budget
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor

noncomputable section
open BianchiIX
open Set



/-- A single small budget cap gives local regularity of every retained original return time. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ Bcap : ℝ, Bcap ≤ Bstar →
          ∀ m : ℕ, ∀ p ∈ eraInputSelection σ Bcap m, ContDiffAt ℝ 1 (eraReturnTime η J m) p.2 := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_time_regular
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨ε, hε, C, hC, HE⟩ := Hδ η hη hηδ J (by omega)
  obtain ⟨Bstar, hBstar, hBone, HB⟩ := exists_retained_era_parameter_budget hε
    (le_trans zero_le_one hC) hσ hσone hσJ
  refine ⟨Bstar, hBstar, hBone, ?_⟩
  intro Bcap hcap m p hp
  obtain ⟨hB, hm, hu, hw, hsum, hr⟩ := hp
  obtain ⟨hβ, hβmax, hsmall, hmargin, hscale⟩ := HB p.1 ⟨hB.1, hB.2.trans hcap⟩
  have hm' : (m : ℝ) + 1 ≤ 1 / p.1 ^ σ :=
    (show (m : ℝ) + 1 ≤ (⌊1 / p.1 ^ σ⌋₊ : ℝ) by exact_mod_cast (Nat.succ_le_of_lt hm)).trans
      (Nat.floor_le (by positivity))
  have hrpos : 0 < p.2 0 := by nlinarith only [hr.1, hβ, Nat.cast_nonneg (α := ℝ) m]
  have hBr : p.1 * p.2 0 ≤ ε :=
    (mul_le_mul_of_nonneg_left hr.2 hB.1.le).trans (hscale m hm')
  have hwall {z : ℝ} (hz : z ≤ p.1) : z ≤ ε / p.2 0 :=
    (le_div_iff₀ hrpos).mpr ((mul_le_mul_of_nonneg_right hz hrpos.le).trans hBr)
  exact HE m (p.1 ^ σ) p.2 hβ (by linarith only [hβmax])
    ⟨hu, hwall (by linarith only [hsum, hw])⟩ ⟨hw, hwall (by linarith only [hsum, hu])⟩
    (hsum.trans hsmall) ⟨by linarith only [hr.1], by linarith only [hr.2]⟩
    ((mul_le_mul_of_nonneg_left hsum (le_trans zero_le_one hC)).trans_lt hmargin)
