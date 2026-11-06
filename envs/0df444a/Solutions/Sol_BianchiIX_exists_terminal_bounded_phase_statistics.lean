-- Prove2me | solution 1 for BianchiIX.exists_terminal_bounded_phase_statistics
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:36:30.31198+00:00
-- url     : https://prove2.me/submissions/a7e048bc-6548-42df-b95d-defc1d4356e0

import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_exists_terminalEntranceInput_derivative_uniform
import Theorems.Thm_BianchiIX_exists_terminal_bounded_phase_error_bound
import Theorems.Thm_BianchiIX_exists_terminal_reciprocal_error_power_bounds
import Theorems.Thm_BianchiIX_exists_terminal_single_phase_composed_bounds
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

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.reciprocal_coordinate_differential_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {f : E → Fin n → ℝ} {x : E} {α D : ℝ} (i : Fin n)
    (hf : ContDiffAt ℝ 2 f x) (hα : 0 < α) (hD : 0 ≤ D)
    (hval : 1 / α ≤ f x i) (hder : ‖fderiv ℝ f x‖ ≤ D / α ^ 2) :
    ContDiffAt ℝ 2 (fun y => 2 / f y i) x ∧
      ∀ v : E, |fderiv ℝ (fun y => 2 / f y i) x v| ≤ 2 * D * ‖v‖ := by
  have hr : 0 < f x i := (one_div_pos.mpr hα).trans_le hval
  have HR := hasFDerivAt_pi'.mp (hf.differentiableAt (by norm_num)).hasFDerivAt i
  have HD := ((hasDerivAt_inv hr.ne').comp_hasFDerivAt x HR).const_mul 2
  change HasFDerivAt (fun y => 2 / f y i) _ x at HD
  refine ⟨contDiffAt_const.div ((contDiffAt_pi.mp hf) i) hr.ne', ?_⟩
  intro v
  have HE : fderiv ℝ (fun y => 2 / f y i) x v = -2 * fderiv ℝ f x v i / (f x i) ^ 2 := by
    rw [HD.fderiv]
    simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    ring
  have Hpart : |fderiv ℝ f x v i| ≤ (D / α ^ 2) * ‖v‖ := (norm_le_pi_norm _ i).trans
    (((fderiv ℝ f x).le_opNorm v).trans (mul_le_mul_of_nonneg_right hder (norm_nonneg v)))
  have Hinv : 1 / f x i ≤ α := (div_le_iff₀ hr).mpr (by
    have H := (div_le_iff₀ hα).mp hval; nlinarith only [H])
  have Hinv2 : 1 / (f x i) ^ 2 ≤ α ^ 2 := by
    simpa only [div_pow, one_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ 1 / f x i) Hinv 2
  rw [HE, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (f x i))]
  norm_num only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ = (2 * |fderiv ℝ f x v i|) * (1 / (f x i) ^ 2) := by ring
    _ ≤ (2 * ((D / α ^ 2) * ‖v‖)) * α ^ 2 := by gcongr
    _ = _ := by field_simp

end
end

private theorem BianchiIX.terminalBoundedPhase_decomposition (h : ℝ) :
    terminalBoundedPhase h = fun Y => terminalSinglePhase h Y + terminalBoundedPhaseError h Y := by
  funext Y
  dsimp [terminalBoundedPhase, terminalSinglePhase, terminalBoundedPhaseError]
  ring

private theorem BianchiIX.terminalBoundedPhase_reciprocal_decomposition (h : ℝ) :
    terminalBoundedPhase h = fun Y => 2 / terminalEntranceInput h Y 0 + terminalReciprocalError h Y := by
  funext Y
  dsimp [terminalBoundedPhase, terminalReciprocalError]
  ring


/-- All estimates of (D.31) concern the actual arrival map at fixed auxiliary height. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η₀ : ℝ, (0 < η₀ ∧ η₀ ≤ δ) →
      ∀ J : ℕ, 4 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ δ → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalBoundedPhase h) Y ∧
        (|terminalBoundedPhase h Y - α| + |fderiv ℝ (terminalBoundedPhase h) Y (Pi.single 0 1) - 1 / 2| ≤ C * b) ∧
        (|fderiv ℝ (terminalBoundedPhase h) Y (Pi.single 1 1)| +
          |fderiv ℝ (terminalBoundedPhase h) Y (Pi.single 2 1)| ≤ C) := by
  obtain ⟨δc, hδc, hδchi, HC⟩ := exists_terminal_bounded_phase_error_bound
  obtain ⟨δp, hδp, _, HP⟩ := exists_terminal_reciprocal_error_power_bounds
  let δ := min δc δp
  have hδhi : δ ≤ 1 / 40000 := (min_le_left _ _).trans hδchi
  refine ⟨δ, lt_min hδc hδp, hδhi, ?_⟩
  intro η₀ hη₀ J hJ
  have hJ2 : 2 ≤ J := by omega
  have hη100 : 0 < η₀ ∧ η₀ ≤ 1 / 100 := ⟨hη₀.1, (hη₀.2.trans hδhi).trans (by norm_num)⟩
  have hη1000 : 0 < η₀ ∧ η₀ ≤ 1 / 1000 := ⟨hη₀.1, (hη₀.2.trans hδhi).trans (by norm_num)⟩
  obtain ⟨A, hA, εa, hεa, HA⟩ := exists_terminal_single_phase_composed_bounds hη100 hJ2
  obtain ⟨B, hB, εb, hεb, HB⟩ := HC η₀ ⟨hη₀.1, hη₀.2.trans (min_le_left _ _)⟩ J hJ
  obtain ⟨P, hP, εp, hεp, HΨ⟩ := HP η₀ ⟨hη₀.1, hη₀.2.trans (min_le_right _ _)⟩ J hJ
  obtain ⟨D, hD, εd, hεd, HD⟩ := exists_terminalEntranceInput_derivative_uniform hη1000 hJ2
  have hP0 : 0 ≤ P := (by norm_num : (0 : ℝ) ≤ 1).trans hP
  have hD0 : 0 ≤ D := (by norm_num : (0 : ℝ) ≤ 1).trans hD
  let C := A + B + 4 * D + 2 * P
  let ε := min εa (min εb (min εp (min εd 1)))
  refine ⟨C, by dsimp only [C]; linarith only [hA, hB, hD, hP],
    ε, lt_min hεa (lt_min hεb (lt_min hεp (lt_min hεd (by norm_num)))), ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum hu hw Y h
  have hs (a : ℝ) (ha : ε ≤ a) : b ≤ a * α ^ (2 * J) :=
    hsmall.trans (mul_le_mul_of_nonneg_right ha (pow_nonneg hα.1.le _))
  have hsa := hs εa (min_le_left _ _)
  have hsb := hs εb ((min_le_right _ _).trans (min_le_left _ _))
  have hsp := hs εp ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsd := hs εd ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hb1 : b ≤ 1 := hsmall.trans ((mul_le_of_le_one_left (pow_nonneg hα.1.le _) hε1).trans
    (pow_le_one₀ hα.1.le hα.2))
  have hηsmall := hηhi.trans hδhi
  obtain ⟨HV, Hsa, Hs, _⟩ := HA η α b u w hηlo (hηsmall.trans (by norm_num)) hα hb hsa hsum
  obtain ⟨_, Hsb, He⟩ := HB η α b u w hηlo (hηhi.trans (min_le_left _ _)) hα hb hsb hsum hu hw
  obtain ⟨_, Hp, _, Hr, _, Hp01, Hp2⟩ := HΨ η α b u w hηlo (hηhi.trans (min_le_right _ _)) hα hb hsp hsum hu hw
  obtain ⟨_, _, Hi, _, Hdi, _⟩ := HD η α b u w hηlo (hηsmall.trans (by norm_num)) hα hb hsd hsum
  have Hsmooth := Hsa.add Hsb
  rw [← terminalBoundedPhase_decomposition h] at Hsmooth
  have HDS := (Hsa.differentiableAt (by norm_num)).hasFDerivAt.add (Hsb.differentiableAt (by norm_num)).hasFDerivAt
  change HasFDerivAt (fun Z => terminalSinglePhase h Z + terminalBoundedPhaseError h Z) _ Y at HDS
  rw [← terminalBoundedPhase_decomposition h] at HDS
  refine ⟨HV, Hsmooth, ?_, ?_⟩
  · have HVeq : terminalBoundedPhase h Y - α = (terminalSinglePhase h Y - α) + terminalBoundedPhaseError h Y := by
      rw [terminalBoundedPhase_decomposition h]; ring
    have HDeq : fderiv ℝ (terminalBoundedPhase h) Y (Pi.single 0 1) - 1 / 2 =
        (fderiv ℝ (terminalSinglePhase h) Y (Pi.single 0 1) - 1 / 2) +
          fderiv ℝ (terminalBoundedPhaseError h) Y (Pi.single 0 1) := by rw [HDS.fderiv, add_apply]; ring
    rw [HVeq, HDeq]
    have H1 := abs_add_le (terminalSinglePhase h Y - α) (terminalBoundedPhaseError h Y)
    have H2 := abs_add_le (fderiv ℝ (terminalSinglePhase h) Y (Pi.single 0 1) - 1 / 2)
      (fderiv ℝ (terminalBoundedPhaseError h) Y (Pi.single 0 1))
    dsimp only [C]
    nlinarith only [H1, H2, Hs, He, (by positivity : 0 ≤ (4 * D + 2 * P) * b)]
  · have Hinv := reciprocal_coordinate_differential_bound 0 Hi hα.1 hD0 Hr Hdi
    have HDR := (Hinv.1.differentiableAt (by norm_num)).hasFDerivAt.add (Hp.differentiableAt (by norm_num)).hasFDerivAt
    change HasFDerivAt (fun Z => 2 / terminalEntranceInput h Z 0 + terminalReciprocalError h Z) _ Y at HDR
    rw [← terminalBoundedPhase_reciprocal_decomposition h] at HDR
    have Hiv (i : Fin 3) : |fderiv ℝ (fun Z => 2 / terminalEntranceInput h Z 0) Y (Pi.single i 1)| ≤ 2 * D := by
      simpa only [Pi.norm_single, norm_one, mul_one] using Hinv.2 (Pi.single i 1)
    have hw1 : w ≤ 1 := by linarith only [hsum, hb1, le_abs_self w, abs_nonneg u]
    have HPw : P * w * α ^ (J - 4) ≤ P :=
      (mul_le_of_le_one_right (mul_nonneg hP0 hw.le) (pow_le_one₀ hα.1.le hα.2)).trans
        (mul_le_of_le_one_right hP0 hw1)
    have Hp1 : |fderiv ℝ (terminalReciprocalError h) Y (Pi.single 1 1)| ≤ P :=
      (le_add_of_nonneg_left (abs_nonneg _)).trans (Hp01.trans HPw)
    have Hp2' : |fderiv ℝ (terminalReciprocalError h) Y (Pi.single 2 1)| ≤ P :=
      Hp2.trans (mul_le_of_le_one_right hP0 (pow_le_one₀ hα.1.le hα.2))
    rw [HDR.fderiv, add_apply, add_apply]
    have H1 := abs_add_le (fderiv ℝ (fun Z => 2 / terminalEntranceInput h Z 0) Y (Pi.single 1 1))
      (fderiv ℝ (terminalReciprocalError h) Y (Pi.single 1 1))
    have H2 := abs_add_le (fderiv ℝ (fun Z => 2 / terminalEntranceInput h Z 0) Y (Pi.single 2 1))
      (fderiv ℝ (terminalReciprocalError h) Y (Pi.single 2 1))
    dsimp only [C]
    linarith only [H1, H2, Hiv 1, Hiv 2, Hp1, Hp2', hA, hB]
