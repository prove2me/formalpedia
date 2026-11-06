-- Prove2me | solution 1 for BianchiIX.exists_era_output_graph_estimates
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:42:54.370757+00:00
-- url     : https://prove2.me/submissions/3769e632-c16a-4295-9330-3ceb661dad7d

import Definitions.Def_BianchiIX_EraReturnData
import Theorems.Thm_BianchiIX_exists_era_output_estimates
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

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.graphPhase_differential {F : (Fin 3 → ℝ) → ℝ} {U W : ℝ → ℝ} {r : ℝ}
    (hF : ContDiffAt ℝ 1 F ![r, U r, W r])
    (hU : ContDiffAt ℝ 1 U r) (hW : ContDiffAt ℝ 1 W r) :
    ContDiffAt ℝ 1 (graphPhase F U W) r ∧
      HasDerivAt (graphPhase F U W)
        (fderiv ℝ F ![r, U r, W r] ![1, deriv U r, deriv W r]) r := by
  let γ := fun t => (![t, U t, W t] : Fin 3 → ℝ)
  have Hγ : ContDiffAt ℝ 1 γ r := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact contDiffAt_id
    · exact hU
    · exact hW
  have HDγ : HasDerivAt γ ![1, deriv U r, deriv W r] r := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hasDerivAt_id r
    · exact (hU.differentiableAt (by norm_num)).hasDerivAt
    · exact (hW.differentiableAt (by norm_num)).hasDerivAt
  exact ⟨hF.comp r Hγ,
    (hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt r HDγ⟩

end
end


/-- The actual era maps every admissible entrance graph to a regular radial curve with uniform output bounds. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C ≥ (1 : ℝ),
      ∀ (m : ℕ) (β B : ℝ) (U W : ℝ → ℝ), 0 < β → β < 1 / 4 →
        let a := 2 * ((m : ℝ) + 1 + β)
        let b := 2 * ((m : ℝ) + 2 - β)
        B * b ≤ ε → B ≤ ε * (β / 2) ^ (2 * J) → C * B < β / 4 →
        (∀ r ∈ Icc a b, 0 < U r ∧ 0 < W r ∧ U r + W r ≤ B ∧
          ContDiffAt ℝ 1 U r ∧ ContDiffAt ℝ 1 W r ∧
          |deriv U r| ≤ Real.sqrt (U r) ∧ |deriv W r| ≤ Real.sqrt (W r)) →
        let k := eraGraphRadius η J m U W
        let u := eraGraphWall η J m U W 1
        let w := eraGraphWall η J m U W 3
        ∀ r ∈ Icc a b, ContDiffAt ℝ 1 k r ∧ deriv k r < 0 ∧
          ContDiffAt ℝ 1 u r ∧ ContDiffAt ℝ 1 w r ∧ 0 < u r ∧ 0 < w r ∧
          u r + w r ≤ C * B ^ (19 / 10 : ℝ) ∧
          |deriv u r| ≤ (C * B ^ (7 / 24 : ℝ)) * (Real.sqrt (u r) * |deriv k r|) ∧
          |deriv w r| ≤ (C * B ^ (7 / 24 : ℝ)) * (Real.sqrt (w r) * |deriv k r|) := by
  obtain ⟨δ, hδ, hδmax, H⟩ := exists_era_output_estimates
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ
  obtain ⟨ε, hε, hεmax, C, hC, HE⟩ := H η hη hηδ J hJ
  refine ⟨ε, hε, hεmax, C, hC, ?_⟩
  intro m β B U W hβ hβmax a b hscale hsmall hmargin Hgraph k u w r hr
  obtain ⟨hu, hw, hsum, hU, hW, hdU, hdW⟩ := Hgraph r hr
  have hC0 : 0 ≤ C := by linarith
  have hB : 0 < B := by linarith
  have hr0 : 0 < r := by dsimp [a] at hr; nlinarith [hr.1, Nat.cast_nonneg (α := ℝ) m]
  have hBr : B * r ≤ ε := (mul_le_mul_of_nonneg_left hr.2 hB.le).trans hscale
  have hwall {z : ℝ} (hz : z ≤ B) : z ≤ ε / r :=
    (le_div_iff₀ hr0).mpr ((mul_le_mul_of_nonneg_right hz hr0.le).trans hBr)
  have hphase : (m : ℝ) + 1 + β ≤ r / 2 ∧ r / 2 ≤ (m : ℝ) + 2 - β := by
    dsimp [a, b] at hr
    constructor <;> linarith [hr.1, hr.2]
  have hUB : U r ≤ B := by linarith
  have hWB : W r ≤ B := by linarith
  obtain ⟨HS, HR, hpu, hpw, hamp, _, HD⟩ := HE m β ![r, U r, W r] hβ (by linarith)
    ⟨hu, hwall hUB⟩ ⟨hw, hwall hWB⟩ (hsum.trans hsmall) hphase
    ((mul_le_mul_of_nonneg_left hsum hC0).trans_lt hmargin)
  obtain ⟨Hk, Hdk⟩ := graphPhase_differential HR hU hW
  have Hwall (i : Fin 4) :
      ContDiffAt ℝ 1 (eraGraphWall η J m U W i) r ∧
      HasDerivAt (eraGraphWall η J m U W i)
        (fderiv ℝ (eraOutputState η J m) ![r, U r, W r] ![1, deriv U r, deriv W r] i) r := by
    obtain ⟨hc, hd⟩ := graphPhase_differential (contDiffAt_pi.mp HS i) hU hW
    rw [fderiv_apply (HS.differentiableAt (by norm_num)) i] at hd
    exact ⟨hc, hd⟩
  obtain ⟨hp, hcone⟩ := HD ![1, deriv U r, deriv W r] rfl hdU hdW
  have hkneg : deriv k r < 0 := Hdk.deriv ▸ hp
  have hc : (C * (U r + W r) ^ (7 / 24 : ℝ)) ≤ C * B ^ (7 / 24 : ℝ) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (add_pos hu hw).le hsum (by norm_num)) hC0
  have hcu := ((le_max_left _ _).trans hcone).trans hc
  have hcw := ((le_max_right _ _).trans hcone).trans hc
  rw [← Hdk.deriv, ← (Hwall 1).2.deriv] at hcu
  rw [← Hdk.deriv, ← (Hwall 3).2.deriv] at hcw
  refine ⟨Hk, hkneg, (Hwall 1).1, (Hwall 3).1, hpu, hpw, ?_, ?_, ?_⟩
  · exact hamp.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (add_pos hu hw).le hsum (by norm_num)) hC0)
  · exact (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr hpu) (abs_pos.mpr hkneg.ne))).mp hcu
  · exact (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr hpw) (abs_pos.mpr hkneg.ne))).mp hcw
