-- Prove2me | solution 1 for BianchiIX.exists_terminal_phase_statistics
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:42:01.054209+00:00
-- url     : https://prove2.me/submissions/8382a7fb-5c4f-48f6-a9f9-91d2b3642cd8

import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_exists_terminal_bounded_phase_statistics
import Theorems.Thm_BianchiIX_reciprocal_small_phase_bounds
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
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
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.ProjIcc
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Notation

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.two_div_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {y : E} (hf : DifferentiableAt ℝ f y) (h0 : f y ≠ 0) (v : E) :
    fderiv ℝ (fun z => 2 / f z) y v = -2 * fderiv ℝ f y v / (f y) ^ 2 := by
  have HD := ((hasDerivAt_inv h0).comp_hasFDerivAt y hf.hasFDerivAt).const_mul 2
  change HasFDerivAt (fun z => 2 / f z) _ y at HD
  rw [HD.fderiv]
  simp only [smul_apply, smul_eq_mul]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.reciprocal_phase_statistics {f : (Fin 3 → ℝ) → ℝ} {y : Fin 3 → ℝ}
    {α A b : ℝ} (hf : ContDiffAt ℝ 2 f y) (hα : 0 < α ∧ α ≤ 1)
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hsmall : A * b ≤ α / 4)
    (herr : |f y - α| + |fderiv ℝ f y (Pi.single 0 1) - 1 / 2| ≤ A * b)
    (hwall : |fderiv ℝ f y (Pi.single 1 1)| + |fderiv ℝ f y (Pi.single 2 1)| ≤ A) :
    0 < f y ∧ ContDiffAt ℝ 2 (fun z => 2 / f z) y ∧
      |2 / f y - 2 / α| ≤ 4 * A * b / α ^ 2 ∧
      |fderiv ℝ (fun z => 2 / f z) y (Pi.single 0 1) + 1 / α ^ 2| ≤ 20 * A * b / α ^ 3 ∧
      |fderiv ℝ (fun z => 2 / f z) y (Pi.single 1 1)| +
        |fderiv ℝ (fun z => 2 / f z) y (Pi.single 2 1)| ≤ 8 * A / α ^ 2 := by
  obtain ⟨hx, Hinv, Hv, Hr⟩ := reciprocal_small_phase_bounds hα hA hb hsmall herr
  have HD := two_div_fderiv (hf.differentiableAt (by norm_num)) hx.ne'
  refine ⟨hx, contDiffAt_const.div hf hx.ne', Hv, by rw [HD]; exact Hr, ?_⟩
  rw [HD, HD]
  simp only [abs_div, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (f y))]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ = 2 * (|fderiv ℝ f y (Pi.single 1 1)| + |fderiv ℝ f y (Pi.single 2 1)|) * (1 / (f y) ^ 2) := by ring
    _ ≤ 2 * A * (4 / α ^ 2) := by gcongr
    _ = _ := by ring

end
end

private theorem BianchiIX.terminalConnectionPhase_two_div_bounded (h : ℝ) :
    terminalConnectionPhase h = fun Y => 2 / terminalBoundedPhase h Y := by
  funext Y
  simp only [terminalBoundedPhase, div_div_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)]


/-- The value and ordinary derivative estimates of (D.33) for the exact terminal arrival phase. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η₀ : ℝ, (0 < η₀ ∧ η₀ ≤ δ) →
      ∀ J : ℕ, 4 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ δ → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalConnectionPhase h) Y ∧
        0 < terminalConnectionPhase h Y ∧
        |terminalConnectionPhase h Y - 2 / α| ≤ C * b / α ^ 2 ∧
        |fderiv ℝ (terminalConnectionPhase h) Y (Pi.single 0 1) + 1 / α ^ 2| ≤ C * b / α ^ 3 ∧
        (|fderiv ℝ (terminalConnectionPhase h) Y (Pi.single 1 1)| +
          |fderiv ℝ (terminalConnectionPhase h) Y (Pi.single 2 1)| ≤ C / α ^ 2) := by
  obtain ⟨δ, hδ, hδhi, HE⟩ := exists_terminal_bounded_phase_statistics
  refine ⟨δ, hδ, hδhi, ?_⟩
  intro η₀ hη₀ J hJ
  obtain ⟨A, hA, ε₀, hε₀, HA⟩ := HE η₀ hη₀ J hJ
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  refine ⟨20 * A, by linarith only [hA], min ε₀ (1 / (4 * A)),
    lt_min hε₀ (by positivity), ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum hu hw Y h
  have hsmall₀ : b ≤ ε₀ * α ^ (2 * J) := hsmall.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le _))
  have hbα : b ≤ (1 / (4 * A)) * α := hsmall.trans
    ((mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg hα.1.le _)).trans
      (mul_le_mul_of_nonneg_left
        (by simpa only [pow_one] using pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 1 ≤ 2 * J))
        (by positivity)))
  have hAb : A * b ≤ α / 4 := (mul_le_mul_of_nonneg_left hbα hA0.le).trans_eq (by field_simp)
  obtain ⟨HV, Hf, Herr, Hwall⟩ := HA η α b u w hηlo hηhi hα hb hsmall₀ hsum hu hw
  obtain ⟨hx, Hk, Hv, Hr, Hw⟩ := reciprocal_phase_statistics Hf hα hA0.le hb.le hAb Herr Hwall
  rw [← terminalConnectionPhase_two_div_bounded h] at Hk Hr Hw
  change |(fun Z => 2 / terminalBoundedPhase h Z) Y - 2 / α| ≤ _ at Hv
  rw [← terminalConnectionPhase_two_div_bounded h] at Hv
  refine ⟨HV, Hk, ?_, ?_, Hr, ?_⟩
  · rw [terminalConnectionPhase_two_div_bounded h]
    exact div_pos (by norm_num) hx
  · exact Hv.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by linarith only [hA] : 4 * A ≤ 20 * A) hb.le) (sq_nonneg α))
  · exact Hw.trans (div_le_div_of_nonneg_right (by linarith only [hA] : 8 * A ≤ 20 * A) (sq_nonneg α))
