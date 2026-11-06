-- Prove2me | solution 1 for BianchiIX.exists_era_inverse_branch_estimates
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:43:54.801834+00:00
-- url     : https://prove2.me/submissions/e97a48da-5fd9-42de-9869-fd20588b8e39

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_EraReturnData
import Theorems.Thm_BianchiIX_exists_era_interval_inverse
import Theorems.Thm_BianchiIX_reciprocal_gauss_estimates
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

noncomputable section
open BianchiIX
open Set



/-- The actual inverse era branch satisfies the Gauss value and logarithmic derivative estimates. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C ≥ (1 : ℝ),
      ∀ (m : ℕ) (β B : ℝ) (U W : ℝ → ℝ), 0 < β → β < 1 / 4 →
        let a := 2 * ((m : ℝ) + 1 + β)
        let b := 2 * ((m : ℝ) + 2 - β)
        B * b ≤ ε → B ≤ ε * (β / 2) ^ (2 * J) → C * B < β / 4 →
        (∀ r ∈ Icc a b, 0 < U r ∧ 0 < W r ∧ U r + W r ≤ B ∧
          ContDiffAt ℝ 1 U r ∧ ContDiffAt ℝ 1 W r ∧
          |deriv U r| ≤ Real.sqrt (U r) ∧ |deriv W r| ≤ Real.sqrt (W r)) →
        let φ := graphPhase (eraBoundedPhase η J m) U W
        let h := eraInverseBranch η J m β U W
        StrictAntiOn h (Icc (2 * β) (1 - 2 * β)) ∧
        ∀ y ∈ Icc (2 * β) (1 - 2 * β),
          h y ∈ Ioo (1 / ((m : ℝ) + 2)) (1 / ((m : ℝ) + 1)) ∧
          φ (2 / h y) = y ∧ ContDiffAt ℝ 1 h y ∧ deriv h y < 0 ∧
          |h y - gaussInv ((m : ℝ) + 1) y| ≤ C * B / ((m : ℝ) + 1) ^ 2 ∧
          |Real.log (|deriv h y| / |deriv (gaussInv ((m : ℝ) + 1)) y|)| ≤
            5 * C * Real.sqrt B := by
  obtain ⟨δ, hδ, hδmax, H⟩ := exists_era_interval_inverse
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ
  obtain ⟨ε, hε, hεmax, C, hC, HE⟩ := H η hη hηδ J hJ
  refine ⟨ε, hε, hεmax, C, hC, ?_⟩
  intro m β B U W hβ hβmax a b hscale hsmall hmargin Hgraph φ h
  obtain ⟨_, _, _, _, HI⟩ := HE m β B U W hβ hβmax hscale hsmall hmargin Hgraph
  let g := intervalRadiusInverse φ a b
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hab : a < b := by dsimp [a, b]; linarith
  have hB : 0 < B := by
    obtain ⟨hu, hw, hsum, _⟩ := Hgraph a ⟨le_rfl, hab.le⟩
    linarith
  have hb1 : 1 ≤ b := by dsimp [b]; linarith
  have hB1 : B ≤ 1 := by
    have Hmul := mul_le_mul_of_nonneg_left hb1 hB.le
    linarith
  have hBsqrt : B ≤ Real.sqrt B := by
    have hs := Real.sq_sqrt hB.le
    have hs0 := Real.sqrt_nonneg B
    nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hB1)]
  have hC0 : 0 ≤ C := by linarith
  have Hpoint (y : ℝ) (hy : y ∈ Icc (2 * β) (1 - 2 * β)) :
      h y ∈ Ioo (1 / ((m : ℝ) + 2)) (1 / ((m : ℝ) + 1)) ∧
      φ (2 / h y) = y ∧ ContDiffAt ℝ 1 h y ∧ deriv h y < 0 ∧
      |h y - gaussInv ((m : ℝ) + 1) y| ≤ C * B / ((m : ℝ) + 1) ^ 2 ∧
      |Real.log (|deriv h y| / |deriv (gaussInv ((m : ℝ) + 1)) y|)| ≤
        5 * C * Real.sqrt B := by
    obtain ⟨hgi, hfg, _, hg, hgd, hgd0, hgv, hgl⟩ := HI y hy
    change g y ∈ Ioo a b at hgi
    have hg0 : 0 < g y := by dsimp [a, b] at hgi; linarith [hgi.1]
    have hhalf : (m : ℝ) + 1 < g y / 2 ∧ g y / 2 < (m : ℝ) + 2 := by
      dsimp [a, b] at hgi
      constructor <;> linarith [hgi.1, hgi.2]
    have hy0 : 0 ≤ y := by linarith [hy.1]
    have Hhalf : HasDerivAt (fun z => g z / 2) (deriv g y / 2) y :=
      (hg.differentiableAt (by norm_num)).hasDerivAt.div_const 2
    have hrec : (fun z => 1 / (g z / 2)) = h := by
      funext z
      change 1 / (g z / 2) = 2 / g z
      ring
    obtain ⟨_, hneg, hv, hl⟩ := reciprocal_gauss_estimates (by linarith : 1 ≤ (m : ℝ) + 1)
      hy0 hhalf.1.le Hhalf (div_pos hgd0 (by norm_num)) hgv (by linarith) hgl
    rw [hrec] at hneg hv hl
    refine ⟨?_, ?_, ?_, hneg, hv, ?_⟩
    · change 2 / g y ∈ _
      rw [show 2 / g y = 1 / (g y / 2) by ring]
      exact ⟨one_div_lt_one_div_of_lt (by positivity) hhalf.2,
        one_div_lt_one_div_of_lt (by positivity) hhalf.1⟩
    · change φ (2 / (2 / g y)) = y
      rw [show 2 / (2 / g y) = g y by field_simp]
      exact hfg
    · exact contDiffAt_const.div hg hg0.ne'
    · have Hsqrt := mul_le_mul_of_nonneg_left hBsqrt hC0
      linarith
  refine ⟨?_, Hpoint⟩
  exact strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (fun y hy => (Hpoint y hy).2.2.1.continuousAt.continuousWithinAt)
    (fun y hy => (Hpoint y (interior_subset hy)).2.2.2.1)
