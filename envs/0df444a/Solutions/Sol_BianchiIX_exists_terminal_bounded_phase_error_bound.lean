-- Prove2me | solution 1 for BianchiIX.exists_terminal_bounded_phase_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:34:25.531894+00:00
-- url     : https://prove2.me/submissions/2de1337c-4747-41fc-ba80-365760678004

import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_exists_terminal_reciprocal_error_power_bounds
import Theorems.Thm_BianchiIX_exists_terminal_single_reciprocal_bounds
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Arsinh
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_terminal_single_reciprocal_linear_bound {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 40000)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 40000 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalSingleReciprocalError h) Y ∧
        |terminalSingleReciprocalError h Y| +
          |fderiv ℝ (terminalSingleReciprocalError h) Y (Pi.single 0 1)| ≤ C * b := by
  obtain ⟨A, hA, ε₀, hε₀, HA⟩ := exists_terminal_single_reciprocal_bounds hη₀ hJ
  have hA0 : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans hA
  refine ⟨6 * A, by linarith only [hA], min ε₀ 1, lt_min hε₀ (by norm_num), ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h
  have hα0 := hα.1
  have hsa := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left ε₀ 1) (pow_nonneg hα.1.le _))
  obtain ⟨HV, Hreg, H0, HD⟩ := HA η α b u w hηlo hηhi hα hb hsa hsum
  have hbb : b ≤ α ^ 2 := hsmall.trans ((mul_le_of_le_one_left (pow_nonneg hα.1.le _) (min_le_right ε₀ 1)).trans
    (pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 2 ≤ 2 * J)))
  have hh : h ≤ α ^ 2 :=
    (mul_le_of_le_one_left (pow_nonneg hα.1.le J) (hηhi.trans (by norm_num))).trans
      (pow_le_pow_of_le_one hα.1.le hα.2 hJ)
  have hu : |u| ≤ b := (le_add_of_nonneg_right (abs_nonneg w)).trans hsum
  have hw : |w| ≤ b := (le_add_of_nonneg_left (abs_nonneg u)).trans hsum
  have hη0 := hη₀.1.trans_le hηlo
  have hN : |u| * (h + b) + w ^ 2 ≤ 3 * b * α ^ 2 := by
    have Hu := mul_le_mul hu (add_le_add hh hbb) (by dsimp only [h]; positivity) hb.le
    have Hw := mul_le_mul hw (hw.trans hbb) (abs_nonneg w) hb.le
    nlinarith only [Hu, Hw, sq_abs w]
  have HDb : A * (|u| * (h + b) + w ^ 2) / α ^ 2 ≤ 3 * A * b :=
    (div_le_iff₀ (sq_pos_of_pos hα.1)).mpr (by nlinarith only [mul_le_mul_of_nonneg_left hN hA0])
  have H0b : A * (|u| * (h + b) + w ^ 2) / α ≤ 3 * A * b := by
    have H : A * (|u| * (h + b) + w ^ 2) / α ≤ 3 * A * b * α :=
      (div_le_iff₀ hα.1).mpr (by nlinarith only [mul_le_mul_of_nonneg_left hN hA0])
    exact H.trans (mul_le_of_le_one_right (by positivity) hα.2)
  exact ⟨HV, Hreg, by linarith only [H0.trans H0b, HD.trans HDb]⟩

end
end

private theorem BianchiIX.terminalBoundedPhaseError_decomposition (h : ℝ) :
    terminalBoundedPhaseError h = fun Y => terminalSingleReciprocalError h Y + terminalReciprocalError h Y := by
  funext Y
  dsimp [terminalBoundedPhaseError, terminalSingleReciprocalError, terminalReciprocalError]
  ring


/-- All corrections between the single-wall phase and the exact arrival phase are O(b), including the ordinary radial derivative. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η₀ : ℝ, (0 < η₀ ∧ η₀ ≤ δ) →
      ∀ J : ℕ, 4 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ δ → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalBoundedPhaseError h) Y ∧
        |terminalBoundedPhaseError h Y| +
          |fderiv ℝ (terminalBoundedPhaseError h) Y (Pi.single 0 1)| ≤ C * b := by
  obtain ⟨δ₀, hδ₀, hδ₀hi, HΨ⟩ := exists_terminal_reciprocal_error_power_bounds
  let δ := min δ₀ (1 / 40000)
  refine ⟨δ, lt_min hδ₀ (by norm_num), min_le_right _ _, ?_⟩
  intro η₀ hη₀ J hJ
  have hη₀' : 0 < η₀ ∧ η₀ ≤ 1 / 40000 := ⟨hη₀.1, hη₀.2.trans (min_le_right _ _)⟩
  obtain ⟨A, hA, εa, hεa, HA⟩ := exists_terminal_single_reciprocal_linear_bound hη₀' (by omega : 2 ≤ J)
  obtain ⟨B, hB, εb, hεb, HB⟩ := HΨ η₀ ⟨hη₀.1, hη₀.2.trans (min_le_left _ _)⟩ J hJ
  have hB0 : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 1).trans hB
  refine ⟨A + 2 * B, by linarith only [hA, hB], min εa εb, lt_min hεa hεb, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum hu hw Y h
  have hsa := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εa εb) (pow_nonneg hα.1.le _))
  have hsb := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right εa εb) (pow_nonneg hα.1.le _))
  obtain ⟨HV, Ha, Hqa⟩ := HA η α b u w hηlo (hηhi.trans (min_le_right _ _)) hα hb hsa hsum
  obtain ⟨_, Hb, _, _, H0, H01, _⟩ := HB η α b u w hηlo (hηhi.trans (min_le_left _ _)) hα hb hsb hsum hu hw
  have hwB : w ≤ b := by linarith only [hsum, le_abs_self w, abs_nonneg u]
  have Hpow (n : ℕ) : B * w * α ^ n ≤ B * b :=
    (mul_le_of_le_one_right (mul_nonneg hB0 hw.le) (pow_le_one₀ hα.1.le hα.2)).trans
      (mul_le_mul_of_nonneg_left hwB hB0)
  have Hval : |terminalReciprocalError h Y| ≤ B * b := H0.trans (Hpow _)
  have Hder : |fderiv ℝ (terminalReciprocalError h) Y (Pi.single 0 1)| ≤ B * b :=
    (le_add_of_nonneg_right (abs_nonneg _)).trans (H01.trans (Hpow _))
  have Hreg := Ha.add Hb
  rw [← terminalBoundedPhaseError_decomposition h] at Hreg
  have HD := (Ha.differentiableAt (by norm_num)).hasFDerivAt.add (Hb.differentiableAt (by norm_num)).hasFDerivAt
  change HasFDerivAt (fun Z => terminalSingleReciprocalError h Z + terminalReciprocalError h Z) _ Y at HD
  rw [← terminalBoundedPhaseError_decomposition h] at HD
  refine ⟨HV, Hreg, ?_⟩
  rw [HD.fderiv, add_apply, terminalBoundedPhaseError_decomposition h]
  have H1 := abs_add_le (terminalSingleReciprocalError h Y) (terminalReciprocalError h Y)
  have H2 := abs_add_le (fderiv ℝ (terminalSingleReciprocalError h) Y (Pi.single 0 1))
    (fderiv ℝ (terminalReciprocalError h) Y (Pi.single 0 1))
  linarith only [H1, H2, Hqa, Hval, Hder]
