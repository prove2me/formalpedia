-- Prove2me | solution 1 for BianchiIX.exists_restartFastShearProjectionPhase_approximation
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:48:33.670557+00:00
-- url     : https://prove2.me/submissions/575f3f3a-f3b4-4c2c-9209-23d69f178021

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_ShearTransportData
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_exists_compact_vanishing_slice_bounds
import Theorems.Thm_BianchiIX_exists_restartSection_radial_approximation
import Theorems.Thm_BianchiIX_exists_restartShearFastEntry_control
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartReferenceRoot_sq {n : ℝ} (hn : n ^ 2 ≤ 1) :
    restartReferenceRoot n ^ 2 = 1 - n ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hn)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restart_coefficients_small {n : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16) :
    0 ≤ restartShearFactor n - 1 ∧ restartShearFactor n - 1 ≤ n ∧
      0 ≤ restartWallFactor n - 1 ∧ restartWallFactor n - 1 ≤ n ∧
      0 ≤ restartShearCoupling n ∧ restartShearCoupling n ≤ n := by
  let z := restartReferenceRoot n
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hz2 : z ^ 2 = 1 - n ^ 2 := restartReferenceRoot_sq (by nlinarith only [hn.1, hn.2])
  have hz1 : z ≤ 1 := by nlinarith only [hz0, hz2, sq_nonneg n]
  have hzhalf : 1 / 2 ≤ z := by nlinarith only [hz0, hz2, hn.1, hn.2]
  have hzsmall : 1 - z ≤ n := by
    nlinarith only [hz2, hn.1, hn.2, mul_nonneg hz0 (sub_nonneg.mpr hz1)]
  have hd : 0 < 2 + z := by positivity
  have hd2 : 0 < 2 * (2 + z) ^ 2 := by positivity
  have ha : restartShearFactor n - 1 = (1 - z) / (2 + z) := by
    dsimp only [restartShearFactor]
    change 3 / (2 + z) - 1 = _
    field_simp
    ring
  have hc : restartWallFactor n - 1 = (1 - z) * (2 * z + 1) / (2 * (2 + z) ^ 2) := by
    dsimp only [restartWallFactor]
    change 9 * (1 + z) / (2 * (2 + z) ^ 2) - 1 = _
    field_simp
    ring
  have ha0 : 0 ≤ restartShearFactor n - 1 := by rw [ha]; positivity
  have ha1 : restartShearFactor n - 1 ≤ n := by
    rw [ha]
    apply le_trans _ hzsmall
    apply (div_le_iff₀ hd).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hz1) (show 0 ≤ 1 + z by positivity)]
  have hc0 : 0 ≤ restartWallFactor n - 1 := by rw [hc]; positivity
  have hc1 : restartWallFactor n - 1 ≤ n := by
    rw [hc]
    apply le_trans _ hzsmall
    apply (div_le_iff₀ hd2).mpr
    exact mul_le_mul_of_nonneg_left (by nlinarith only [hz0, sq_nonneg z]) (sub_nonneg.mpr hz1)
  have hk0 : 0 ≤ restartShearCoupling n := by
    dsimp only [restartShearCoupling]
    exact div_nonneg (mul_nonneg (by positivity) hn.1) (sq_nonneg _)
  have hk1 : restartShearCoupling n ≤ n := by
    dsimp only [restartShearCoupling]
    change 3 * Real.sqrt 3 * n / (2 + z) ^ 2 ≤ n
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    have hsqrt : Real.sqrt 3 ≤ 2 := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
    have H : 3 * Real.sqrt 3 ≤ (2 + z) ^ 2 := by
      nlinarith only [hsqrt, hzhalf, sq_nonneg (z - 1 / 2)]
    nlinarith only [mul_le_mul_of_nonneg_right H hn.1]
  exact ⟨ha0, ha1, hc0, hc1, hk0, hk1⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_sq (a b : ℝ) : phaseNorm a b ^ 2 = a ^ 2 + b ^ 2 :=
  Real.sq_sqrt (by positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_le_abs_add (a b : ℝ) : phaseNorm a b ≤ |a| + |b| := by
  have hr : 0 ≤ phaseNorm a b := Real.sqrt_nonneg _
  have hs := phaseNorm_sq a b
  nlinarith only [hr, hs, sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b,
    mul_nonneg (abs_nonneg a) (abs_nonneg b)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_cauchy (a b c d : ℝ) :
    |a * c + b * d| ≤ phaseNorm a b * phaseNorm c d := by
  have hP : 0 ≤ phaseNorm a b := Real.sqrt_nonneg _
  have hQ : 0 ≤ phaseNorm c d := Real.sqrt_nonneg _
  have hsq : (a * c + b * d) ^ 2 ≤ (phaseNorm a b * phaseNorm c d) ^ 2 := by
    rw [mul_pow, phaseNorm_sq, phaseNorm_sq]
    nlinarith only [sq_nonneg (a * d - b * c)]
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hP hQ)).mp (by simpa using hsq)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_phaseNorm_affine_bounds {a b c d ρ ζ : ℝ}
    (hP : 0 < phaseNorm a b) (hρ : 0 < ρ) (hζ : 0 ≤ ζ)
    (hsmall : 3 * ζ * phaseNorm c d ≤ ρ * phaseNorm a b) :
    ∃ v : ℝ,
      HasDerivAt (fun x : ℝ => phaseNorm (a * x - c * ζ) (b * x - d * ζ)) v ρ ∧
      phaseNorm a b / 2 ≤ v ∧ v ≤ phaseNorm a b := by
  let P := phaseNorm a b
  let Q := phaseNorm c d
  let R := phaseNorm (a * ρ - c * ζ) (b * ρ - d * ζ)
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hC := (abs_le.mp (phaseNorm_cauchy a b c d)).2
  have hC' := (abs_le.mp (phaseNorm_cauchy a b c d)).1
  have hRsq : R ^ 2 = (ρ * P) ^ 2 - 2 * ρ * ζ * (a * c + b * d) + (ζ * Q) ^ 2 := by
    dsimp only [R, P, Q]
    rw [phaseNorm_sq, mul_pow, mul_pow, phaseNorm_sq, phaseNorm_sq]
    ring
  have hPQ : 0 < ρ * P := mul_pos hρ hP
  have hlowpos : 0 < ρ * P - ζ * Q := by
    change 3 * ζ * Q ≤ ρ * P at hsmall
    nlinarith only [hsmall, hPQ, mul_nonneg hζ hQ]
  have hcross := mul_le_mul_of_nonneg_left hC (show 0 ≤ 2 * ρ * ζ by positivity)
  have hcross' := mul_le_mul_of_nonneg_left hC' (show 0 ≤ 2 * ρ * ζ by positivity)
  change _ ≤ 2 * ρ * ζ * (P * Q) at hcross
  change 2 * ρ * ζ * (-(P * Q)) ≤ _ at hcross'
  have hlow : ρ * P - ζ * Q ≤ R := by
    nlinarith only [hRsq, hcross, hlowpos, hR]
  have hupp : R ≤ ρ * P + ζ * Q := by
    nlinarith only [hRsq, hcross', hPQ, mul_nonneg hζ hQ, hR]
  have hRpos : 0 < R := hlowpos.trans_le hlow
  have hnz : (a * ρ - c * ζ) ^ 2 + (b * ρ - d * ζ) ^ 2 ≠ 0 := by
    have H := phaseNorm_sq (a * ρ - c * ζ) (b * ρ - d * ζ)
    change R ^ 2 = _ at H
    nlinarith only [H, sq_pos_of_pos hRpos]
  let v := (a * (a * ρ - c * ζ) + b * (b * ρ - d * ζ)) / R
  have Hv : HasDerivAt (fun x : ℝ => phaseNorm (a * x - c * ζ) (b * x - d * ζ)) v ρ := by
    have Ha := ((hasDerivAt_id ρ).const_mul a).sub_const (c * ζ)
    have Hb := ((hasDerivAt_id ρ).const_mul b).sub_const (d * ζ)
    convert! ((Ha.pow 2).add (Hb.pow 2)).sqrt hnz using 1
    dsimp only [v, R, phaseNorm]
    simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    ring
  have hid : a * (a * ρ - c * ζ) + b * (b * ρ - d * ζ) = ρ * P ^ 2 - ζ * (a * c + b * d) := by
    dsimp only [P]
    rw [phaseNorm_sq]
    ring
  refine ⟨v, Hv, (le_div_iff₀ hRpos).mpr ?_, (div_le_iff₀ hRpos).mpr ?_⟩
  · have H₁ := mul_le_mul_of_nonneg_left hC hζ
    have H₂ := mul_le_mul_of_nonneg_left hupp hP.le
    have H₃ := mul_le_mul_of_nonneg_left hsmall hP.le
    change _ ≤ ζ * (P * Q) at H₁
    rw [hid]
    nlinarith only [H₁, H₂, H₃]
  · exact (abs_le.mp (phaseNorm_cauchy a b (a * ρ - c * ζ) (b * ρ - d * ζ))).2

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasFDerivAt_normalizedMaxCurve_initial {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (normalizedFlowDifferential x t₀ t) x := by
  have H := (normalizedMaxCurve_regular ht).2.comp x (contDiffAt_id.prodMk contDiffAt_const)
  exact (H.differentiableAt (by norm_num)).hasFDerivAt

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionChart_constraint {h : ℝ} {Z : RestartCenterState}
    (hZ : 0 ≤ restartSectionRadicand h Z) : stateConstraint (restartSectionChart h Z) = 1 := by
  have H := Real.sq_sqrt hZ
  dsimp [stateConstraint, constraint, shearSq, restartSectionChart]
  rw [neg_sq, H]
  unfold restartSectionRadicand
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_restartSectionChart {h : ℝ} {Z : RestartCenterState}
    (hZ : 0 < restartSectionRadicand h Z) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (restartSectionChart h) Z := by
  have hr : ContDiff ℝ k (restartSectionRadicand h) := by
    unfold restartSectionRadicand curvature
    fun_prop
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact (hr.contDiffAt.sqrt hZ.ne').neg
  · exact contDiffAt_apply ℝ ℝ (0 : Fin 3) Z
  · exact contDiffAt_const
  · exact contDiffAt_apply ℝ ℝ (1 : Fin 3) Z
  · exact contDiffAt_apply ℝ ℝ (2 : Fin 3) Z

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionHeight_of_constraint {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) :
    restartProjectionHeight (x 2, ![x 1, x 3, x 4]) = 1 + x 0 := by
  have hd : restartProjectionDefect (x 2, ![x 1, x 3, x 4]) = 1 - (x 0) ^ 2 := by
    change (x 1) ^ 2 + curvature (x 2) (x 3) (x 4) = _
    dsimp only [stateConstraint, constraint, shearSq] at hc
    linarith only [hc]
  have hden : 1 - x 0 ≠ 0 := by linarith only [hp]
  rw [restartProjectionHeight, hd, show 1 - (1 - (x 0) ^ 2) = (x 0) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_neg hp]
  change (1 - x 0 ^ 2) / (1 - x 0) = 1 + x 0
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionPhase_eq_core {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) (hA : 0 < 1 + x 0) :
    restartProjectionPhase (x 2, ![x 1, x 3, x 4]) =
      2 / coreRadius (toProjectiveState x 0) (toProjectiveState x 2) := by
  have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hcore : coreRadius (toProjectiveState x 0) (toProjectiveState x 2) =
      Real.sqrt ((Real.sqrt 3 * x 1 - (1 + x 0)) ^ 2 + 3 * (x 3) ^ 2) / (1 + x 0) := by
    unfold coreRadius coreEnergy
    change Real.sqrt ((projectiveCoord (x 0) (x 1) - 1) ^ 2 +
      projectiveCoord (x 0) (x 3) ^ 2) = _
    have hid : (projectiveCoord (x 0) (x 1) - 1) ^ 2 + projectiveCoord (x 0) (x 3) ^ 2 =
        ((Real.sqrt 3 * x 1 - (1 + x 0)) ^ 2 + 3 * (x 3) ^ 2) / (1 + x 0) ^ 2 := by
      unfold projectiveCoord
      field_simp
      nlinarith only [hsqrt]
    rw [hid, Real.sqrt_div (by positivity), Real.sqrt_sq hA.le]
  rw [restartProjectionPhase, restartProjectionHeight_of_constraint hc hp, hcore]
  change 2 * (1 + x 0) / Real.sqrt ((Real.sqrt 3 * x 1 - (1 + x 0)) ^ 2 + 3 * x 3 ^ 2) = _
  rw [div_div_eq_mul_div]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_restartSectionProjectionPhase_eq_core {h T : ℝ} {Z : RestartCenterState}
    (hrad : 0 < restartSectionRadicand h Z) (hT : 0 ≤ T)
    (hneg : normalizedMaxCurve (restartSectionChart h Z) 0 T 0 < 0)
    (hheight : 0 < 1 + normalizedMaxCurve (restartSectionChart h Z) 0 T 0) :
    (fun W => restartProjectionPhase (restartSectionRadialState h T W)) =ᶠ[𝓝 Z]
      (fun W => let x := normalizedMaxCurve (restartSectionChart h W) 0 T
        2 / coreRadius (toProjectiveState x 0) (toProjectiveState x 2)) := by
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  have Hchart := (contDiffAt_restartSectionChart hrad 1).continuousAt
  have Hflow := (hasFDerivAt_normalizedMaxCurve_initial hdom).continuousAt.comp Hchart
  have Hcoord : ContinuousAt (fun W => normalizedMaxCurve (restartSectionChart h W) 0 T 0) Z :=
    (continuous_apply 0).continuousAt.comp Hflow
  have HR : ContinuousAt (restartSectionRadicand h) Z := by
    unfold restartSectionRadicand curvature
    fun_prop
  have HnearR := HR.eventually (isOpen_Ioi.mem_nhds hrad)
  have HnearN := Hcoord.eventually (isOpen_Iio.mem_nhds hneg)
  have HnearA := (continuousAt_const.add Hcoord).eventually (isOpen_Ioi.mem_nhds hheight)
  filter_upwards [HnearR, HnearN, HnearA] with W hW hN hA
  have HC := (normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hW.le) hT).2.1
  exact restartProjectionPhase_eq_core HC hN hA

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionDefect_scaled (p : RestartProjectionParameters) :
    restartProjectionDefect (restartProjectionScaledState p) =
      (p.1 0) ^ 2 * restartProjectionScaledDefect p := by
  unfold restartProjectionDefect restartProjectionScaledState restartProjectionScaledDefect curvature
  dsimp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionHeight_scaled (p : RestartProjectionParameters) :
    restartProjectionHeight (restartProjectionScaledState p) =
      (p.1 0) ^ 2 * restartProjectionScaledHeight p := by
  rw [restartProjectionHeight, restartProjectionDefect_scaled]
  unfold restartProjectionScaledHeight
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionPhase_scaled {p : RestartProjectionParameters} (hr : 0 < p.1 0) :
    restartProjectionPhase (restartProjectionScaledState p) -
      restartRadialPhase (restartProjectionScaledState p).2 =
        p.1 0 * restartProjectionScaledError p := by
  have hden : (Real.sqrt 3 * (restartProjectionScaledState p).2 0 -
      restartProjectionHeight (restartProjectionScaledState p)) ^ 2 +
      3 * ((restartProjectionScaledState p).2 1) ^ 2 =
        (p.1 0) ^ 2 * restartProjectionScaledDenom p := by
    rw [restartProjectionHeight_scaled]
    dsimp only [restartProjectionScaledState, restartProjectionScaledDenom]
    change (Real.sqrt 3 * (p.1 0 * p.2 0) - (p.1 0) ^ 2 * restartProjectionScaledHeight p) ^ 2 +
      3 * (p.1 0 * p.2 1) ^ 2 = _
    ring
  have hrad : restartRadialNorm (restartProjectionScaledState p).2 =
      p.1 0 * Real.sqrt ((p.2 0) ^ 2 + (p.2 1 - p.1 2) ^ 2) := by
    unfold restartRadialNorm
    change Real.sqrt ((p.1 0 * p.2 0) ^ 2 + (p.1 0 * p.2 1 - p.1 0 * p.1 2) ^ 2) = _
    rw [show (p.1 0 * p.2 0) ^ 2 + (p.1 0 * p.2 1 - p.1 0 * p.1 2) ^ 2 =
      (p.1 0) ^ 2 * ((p.2 0) ^ 2 + (p.2 1 - p.1 2) ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr.le]
  rw [restartProjectionPhase, hden, restartProjectionHeight_scaled,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr.le, restartRadialPhase, hrad]
  unfold restartProjectionScaledError
  rw [show 2 * (p.1 0 ^ 2 * restartProjectionScaledHeight p) =
    p.1 0 * (p.1 0 * (2 * restartProjectionScaledHeight p)) by ring,
    mul_div_mul_left _ _ hr.ne']
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionScaledError_axis (X : RestartProjectionCenter) :
    restartProjectionScaledError (0, X) = 0 := by
  have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hden : restartProjectionScaledDenom (0, X) = 3 * ((X 0) ^ 2 + (X 1) ^ 2) := by
    simp only [restartProjectionScaledDenom, Pi.zero_apply, zero_mul, sub_zero, mul_pow, hsqrt]
    ring
  have hheight : restartProjectionScaledHeight (0, X) = ((X 0) ^ 2 + (X 1) ^ 2) / 2 := by
    norm_num [restartProjectionScaledHeight, restartProjectionScaledDefect, curvature]
  rw [restartProjectionScaledError, hden, hheight, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
  simp only [Pi.zero_apply, sub_zero]
  let R := Real.sqrt ((X 0) ^ 2 + (X 1) ^ 2)
  have hR : R ^ 2 = (X 0) ^ 2 + (X 1) ^ 2 := Real.sq_sqrt (by positivity)
  change 2 * (((X 0) ^ 2 + (X 1) ^ 2) / 2) / (Real.sqrt 3 * R) - R / Real.sqrt 3 = 0
  rw [← hR]
  by_cases hR0 : R = 0
  · simp [hR0]
  · have h3 : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartProjectionScaledError {p : RestartProjectionParameters}
    (hr : 0 < 1 - (p.1 0) ^ 2 * restartProjectionScaledDefect p)
    (hd : 0 < restartProjectionScaledDenom p)
    (hv : 0 < (p.2 0) ^ 2 + (p.2 1 - p.1 2) ^ 2) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartProjectionScaledError p := by
  have HD : ContDiffAt ℝ k restartProjectionScaledDefect p := by
    unfold restartProjectionScaledDefect curvature
    fun_prop
  have HR : ContDiffAt ℝ k (fun q : RestartProjectionParameters =>
      1 - (q.1 0) ^ 2 * restartProjectionScaledDefect q) p := by fun_prop
  have HA : ContDiffAt ℝ k restartProjectionScaledHeight p := by
    apply HD.div ((contDiffAt_const).add (HR.sqrt hr.ne'))
    exact ne_of_gt (by positivity : 0 < 1 + Real.sqrt (1 - (p.1 0) ^ 2 * restartProjectionScaledDefect p))
  have Hden : ContDiffAt ℝ k restartProjectionScaledDenom p := by
    unfold restartProjectionScaledDenom
    fun_prop
  apply ((contDiffAt_const.mul HA).div (Hden.sqrt hd.ne') (ne_of_gt (Real.sqrt_pos.mpr hd))).sub
  have HV : ContDiffAt ℝ k (fun q : RestartProjectionParameters =>
      (q.2 0) ^ 2 + (q.2 1 - q.1 2) ^ 2) p := by fun_prop
  exact (HV.sqrt hv.ne').div_const _

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartProjectionDefect {p : ℝ → RestartRadialState}
    {v : RestartRadialState} {t : ℝ} (H : HasDerivAt p v t) :
    HasDerivAt (fun x => restartProjectionDefect (p x))
      (restartProjectionDefectTangent (p t) v) t := by
  have Hn : HasDerivAt (fun x => (p x).1) v.1 t :=
    (ContinuousLinearMap.fst ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt t H
  have Hc (i : Fin 3) : HasDerivAt (fun x => (p x).2 i) (v.2 i) t := by
    let P : RestartCenterState →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact P.hasFDerivAt.comp_hasDerivAt t
      ((ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt t H)
  have HD := ((Hc 0).pow 2).add
    ((((Hn.pow 2).add ((Hc 1).pow 2)).add ((Hc 2).pow 2)).const_mul 2)
  have HD' := HD.sub (((Hn.add (Hc 1)).add (Hc 2)).pow 2)
  convert! HD' using 1
  · funext x
    dsimp [restartProjectionDefect, curvature]
    ring
  · dsimp [restartProjectionDefectTangent]
    ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartProjectionDefectTangent_bound {p v : RestartRadialState} {R D : ℝ}
    (hp : ‖p‖ ≤ R) (hv : ‖v‖ ≤ D) :
    |restartProjectionDefectTangent p v| ≤ 32 * R * D := by
  have hR : 0 ≤ R := (norm_nonneg p).trans hp
  have hD : 0 ≤ D := (norm_nonneg v).trans hv
  have pn : |p.1| ≤ R := (norm_fst_le p).trans hp
  have pc (i : Fin 3) : |p.2 i| ≤ R := (norm_le_pi_norm p.2 i).trans ((norm_snd_le p).trans hp)
  have vn : |v.1| ≤ D := (norm_fst_le v).trans hv
  have vc (i : Fin 3) : |v.2 i| ≤ D := (norm_le_pi_norm v.2 i).trans ((norm_snd_le v).trans hv)
  have ps : |p.1 + p.2 1 + p.2 2| ≤ 3 * R :=
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (by linarith only [pn, pc 1, pc 2])
  have vs : |v.1 + v.2 1 + v.2 2| ≤ 3 * D :=
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (by linarith only [vn, vc 1, vc 2])
  have Hsum : |p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2| ≤ 3 * R * D := by
    calc
      _ ≤ |p.1 * v.1| + |p.2 1 * v.2 1| + |p.2 2 * v.2 2| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ R * D + R * D + R * D := by
        simp only [abs_mul]
        gcongr
        · exact pc 1
        · exact vc 1
        · exact pc 2
        · exact vc 2
      _ = _ := by ring
  unfold restartProjectionDefectTangent
  calc
    _ ≤ |2 * p.2 0 * v.2 0| + |4 * (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2)| +
        |2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)| := by
      have HT : |2 * p.2 0 * v.2 0 + 4 * (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2) -
          2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)| ≤
          |2 * p.2 0 * v.2 0 + 4 * (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2)| +
          |2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)| := by
        simpa using (abs_sub_le (2 * p.2 0 * v.2 0 + 4 *
          (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2)) 0
          (2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)))
      exact HT.trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * R * D + 4 * (3 * R * D) + 2 * (3 * R) * (3 * D) := by
      norm_num only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      gcongr
      · exact pc 0
      · exact vc 0
    _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartProjectionHeight_eq_sqrt {p : RestartRadialState}
    (hd : restartProjectionDefect p ≤ 1) :
    restartProjectionHeight p = 1 - Real.sqrt (1 - restartProjectionDefect p) := by
  have Hsq := Real.sq_sqrt (by linarith only [hd] : 0 ≤ 1 - restartProjectionDefect p)
  apply (div_eq_iff (by positivity : 1 + Real.sqrt (1 - restartProjectionDefect p) ≠ 0)).mpr
  nlinarith only [Hsq]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartProjectionHeight {p : ℝ → RestartRadialState}
    {v : RestartRadialState} {t : ℝ} (H : HasDerivAt p v t)
    (hd : restartProjectionDefect (p t) < 1) :
    HasDerivAt (fun x => restartProjectionHeight (p x))
      (restartProjectionDefectTangent (p t) v / (2 * Real.sqrt (1 - restartProjectionDefect (p t)))) t := by
  have HD := hasDerivAt_restartProjectionDefect H
  have HS := ((HD.const_sub 1).sqrt (by linarith only [hd] : 1 - restartProjectionDefect (p t) ≠ 0)).const_sub 1
  have Heq : (fun x => restartProjectionHeight (p x)) =ᶠ[𝓝 t]
      fun x => 1 - Real.sqrt (1 - restartProjectionDefect (p x)) := by
    filter_upwards [HD.continuousAt.eventually (isOpen_Iio.mem_nhds hd)] with x hx
    exact restartProjectionHeight_eq_sqrt hx.le
  convert! HS.congr_of_eventuallyEq Heq using 1
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartProjectionHeight_derivative_bound {p : ℝ → RestartRadialState}
    {v : RestartRadialState} {t R D : ℝ} (H : HasDerivAt p v t)
    (hd : restartProjectionDefect (p t) ≤ 1 / 2) (hp : ‖p t‖ ≤ R) (hv : ‖v‖ ≤ D) :
    DifferentiableAt ℝ (fun x => restartProjectionHeight (p x)) t ∧
      |deriv (fun x => restartProjectionHeight (p x)) t| ≤ 32 * R * D := by
  have HD := hasDerivAt_restartProjectionHeight H (by linarith only [hd])
  refine ⟨HD.differentiableAt, ?_⟩
  rw [HD.deriv, abs_div, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt (1 - restartProjectionDefect (p t)))]
  have hsqrt : 1 / 2 ≤ Real.sqrt (1 - restartProjectionDefect (p t)) := by
    have Hsq := Real.sq_sqrt (by linarith only [hd] : 0 ≤ 1 - restartProjectionDefect (p t))
    nlinarith only [Hsq, Real.sqrt_nonneg (1 - restartProjectionDefect (p t)), hd]
  exact (div_le_self (abs_nonneg _) (by linarith only [hsqrt])).trans
    (restartProjectionDefectTangent_bound hp hv)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartProjectionScaledError_direction_bound {u du : RestartProjectionNormal}
    {X dX : RestartProjectionCenter} {C : ℝ}
    (HD : ‖fderiv ℝ restartProjectionScaledError (u, X)‖ ≤ C)
    (HT : ∀ w : RestartProjectionCenter,
      |fderiv ℝ restartProjectionScaledError (u, X) (0, w)| ≤ C * ‖u‖ * ‖w‖) :
    |fderiv ℝ restartProjectionScaledError (u, X) (du, dX)| ≤ C * ‖du‖ + C * ‖u‖ * ‖dX‖ := by
  have HN : |fderiv ℝ restartProjectionScaledError (u, X) (du, 0)| ≤ C * ‖du‖ := by
    have H := ((fderiv ℝ restartProjectionScaledError (u, X)).le_opNorm (du, 0)).trans
      (mul_le_mul_of_nonneg_right HD (norm_nonneg (du, (0 : RestartProjectionCenter))))
    simpa only [Real.norm_eq_abs, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg du)] using H
  have heq : (du, dX) = (du, (0 : RestartProjectionCenter)) + ((0 : RestartProjectionNormal), dX) := by simp
  rw [heq, map_add]
  exact (abs_add_le _ _).trans (add_le_add HN (HT dX))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionDefect_shear_bounds {p : RestartRadialState} {a σ : ℝ}
    (ha : 0 < a ∧ a ≤ 1 / 128) (hσ : |σ| = 1)
    (hs : 3 * a / 4 ≤ σ * p.2 0 ∧ σ * p.2 0 ≤ 9 * a / 4)
    (hn : 0 ≤ p.1 ∧ p.1 ≤ a ^ 2)
    (h₂ : 0 ≤ p.2 1 ∧ p.2 1 ≤ a / 16) (h₃ : 0 ≤ p.2 2 ∧ p.2 2 ≤ a / 16) :
    a ^ 2 / 2 ≤ restartProjectionDefect p ∧ restartProjectionDefect p ≤ 6 * a ^ 2 := by
  have hsig : σ ^ 2 = 1 := by nlinarith only [sq_abs σ, hσ]
  have hsq : (σ * p.2 0) ^ 2 = (p.2 0) ^ 2 := by rw [mul_pow, hsig, one_mul]
  have hslo := pow_le_pow_left₀ (by positivity [ha.1] : 0 ≤ 3 * a / 4) hs.1 2
  have hshi := pow_le_pow_left₀ (by linarith only [hs.1, ha.1] : 0 ≤ σ * p.2 0) hs.2 2
  rw [hsq] at hslo hshi
  have hsum : p.2 1 + p.2 2 ≤ a / 8 := by linarith only [h₂.2, h₃.2]
  have hcross := mul_le_mul hn.2 hsum (add_nonneg h₂.1 h₃.1) (sq_nonneg a)
  have ha1 : a ≤ 1 := by linarith only [ha.2]
  have ha3 : a ^ 2 * a ≤ a ^ 2 := by simpa only [mul_one] using mul_le_mul_of_nonneg_left ha1 (sq_nonneg a)
  have hnsq := pow_le_pow_left₀ hn.1 hn.2 2
  have hdiff : |p.2 1 - p.2 2| ≤ a / 16 :=
    abs_le.mpr ⟨by linarith only [h₂.1, h₃.2], by linarith only [h₃.1, h₂.2]⟩
  have hdsq := pow_le_pow_left₀ (abs_nonneg _) hdiff 2
  rw [sq_abs] at hdsq
  have heq : restartProjectionDefect p = (p.2 0) ^ 2 + p.1 ^ 2 + (p.2 1 - p.2 2) ^ 2 -
      2 * p.1 * (p.2 1 + p.2 2) := by unfold restartProjectionDefect curvature; ring
  constructor
  · rw [heq]
    have ha3small := mul_le_mul_of_nonneg_left ha.2 (sq_nonneg a)
    nlinarith only [hslo, hcross, ha3small, sq_nonneg p.1, sq_nonneg (p.2 1 - p.2 2), sq_nonneg a]
  · rw [heq]
    have hneg := mul_nonneg hn.1 (add_nonneg h₂.1 h₃.1)
    have hnsmall := mul_le_mul_of_nonneg_left ha.2 ha.1.le
    have hn4small := mul_le_mul_of_nonneg_left hnsmall (sq_nonneg a)
    nlinarith only [hshi, hnsq, hn4small, hdsq, hneg, ha3, sq_nonneg a]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionHeight_shear_bounds {p : RestartRadialState} {a σ : ℝ}
    (ha : 0 < a ∧ a ≤ 1 / 128) (hσ : |σ| = 1)
    (hs : 3 * a / 4 ≤ σ * p.2 0 ∧ σ * p.2 0 ≤ 9 * a / 4)
    (hn : 0 ≤ p.1 ∧ p.1 ≤ a ^ 2)
    (h₂ : 0 ≤ p.2 1 ∧ p.2 1 ≤ a / 16) (h₃ : 0 ≤ p.2 2 ∧ p.2 2 ≤ a / 16) :
    restartProjectionDefect p ≤ 1 / 2 ∧
      a ^ 2 / 4 ≤ restartProjectionHeight p ∧ restartProjectionHeight p ≤ 6 * a ^ 2 := by
  obtain ⟨Hlo, Hhi⟩ := restartProjectionDefect_shear_bounds ha hσ hs hn h₂ h₃
  have hd0 : 0 ≤ restartProjectionDefect p := le_trans (by positivity) Hlo
  have hd1 : restartProjectionDefect p ≤ 1 / 2 := by nlinarith only [Hhi, ha.1, ha.2]
  have hsqrt := Real.sqrt_nonneg (1 - restartProjectionDefect p)
  have hsqrt1 : Real.sqrt (1 - restartProjectionDefect p) ≤ 1 := by rw [Real.sqrt_le_one]; linarith only [hd0]
  have hden : 0 < 1 + Real.sqrt (1 - restartProjectionDefect p) := by positivity
  refine ⟨hd1, (le_div_iff₀ hden).mpr ?_, (div_le_iff₀ hden).mpr ?_⟩
  · nlinarith only [Hlo, mul_le_mul_of_nonneg_left hsqrt1 (sq_nonneg a)]
  · nlinarith only [Hhi, mul_nonneg (sq_nonneg a) hsqrt]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionScaledState_parameters {r : ℝ} (hr : r ≠ 0) (p : RestartRadialState) :
    restartProjectionScaledState (restartProjectionParametersAt r p) = p := by
  apply Prod.ext
  · change r * (p.1 / r) = p.1
    field_simp
  · ext i
    fin_cases i <;> change r * (_ / r) = _ <;> field_simp <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionError_rescaled {r : ℝ} (hr : 0 < r) (p : RestartRadialState) :
    restartProjectionError p = r * restartProjectionScaledError (restartProjectionParametersAt r p) := by
  have H := restartProjectionPhase_scaled (p := restartProjectionParametersAt r p) hr
  rw [restartProjectionScaledState_parameters hr.ne'] at H
  exact H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartProjectionParametersAt {p : ℝ → RestartRadialState} {v : RestartRadialState}
    {t : ℝ} (H : HasDerivAt p v t) (r : ℝ) :
    HasDerivAt (fun s => restartProjectionParametersAt r (p s)) (restartProjectionParameterTangent r v) t := by
  have Hfst : HasDerivAt (fun s => (p s).1) v.1 t :=
    (ContinuousLinearMap.fst ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt t H
  have Hsnd : HasDerivAt (fun s => (p s).2) v.2 t :=
    (ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt t H
  have HN : HasDerivAt (fun s => (restartProjectionParametersAt r (p s)).1)
      (restartProjectionParameterTangent r v).1 t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert! hasDerivAt_const t r using 1
    · convert! Hfst.div_const r using 1
    · convert! (hasDerivAt_pi.mp Hsnd 2).div_const r using 1
  have HC : HasDerivAt (fun s => (restartProjectionParametersAt r (p s)).2)
      (restartProjectionParameterTangent r v).2 t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert! (hasDerivAt_pi.mp Hsnd 0).div_const r using 1
    · convert! (hasDerivAt_pi.mp Hsnd 1).div_const r using 1
  exact HN.prodMk HC

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartProjectionError {p : ℝ → RestartRadialState} {v : RestartRadialState}
    {r t : ℝ} (hr : 0 < r) (Hp : HasDerivAt p v t)
    (H : DifferentiableAt ℝ restartProjectionScaledError (restartProjectionParametersAt r (p t))) :
    HasDerivAt (fun s => restartProjectionError (p s))
      (r * fderiv ℝ restartProjectionScaledError (restartProjectionParametersAt r (p t))
        (restartProjectionParameterTangent r v)) t := by
  have HD := (H.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_restartProjectionParametersAt Hp r)).const_mul r
  simpa only [Function.comp_apply, restartProjectionError_rescaled hr] using HD

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiffAt_restartProjectionScaledError_shear_axis {X : RestartProjectionCenter}
    (hs : X 0 ≠ 0) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartProjectionScaledError (0, X) := by
  apply contDiffAt_restartProjectionScaledError
  · simp
  · simp only [restartProjectionScaledDenom, Pi.zero_apply, zero_mul, sub_zero, mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    nlinarith only [sq_pos_of_ne_zero hs, sq_nonneg (X 1)]
  · simp only [Pi.zero_apply, sub_zero]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hs) (sq_nonneg _)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_shearRestartProjectionScaledError_bounds {c M : ℝ} (hc : 0 < c) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (1 : ℝ),
      ∀ X : RestartProjectionCenter, c ≤ |X 0| → |X 0| ≤ M → |X 1| ≤ M →
        ∀ u : RestartProjectionNormal, ‖u‖ ≤ δ →
          ContDiffAt ℝ 2 restartProjectionScaledError (u, X) ∧
          |restartProjectionScaledError (u, X)| ≤ C * ‖u‖ ∧
          ‖fderiv ℝ restartProjectionScaledError (u, X)‖ ≤ C ∧
          ∀ w : RestartProjectionCenter,
            |fderiv ℝ restartProjectionScaledError (u, X) (0, w)| ≤ C * ‖u‖ * ‖w‖ := by
  let K : Set RestartProjectionCenter := Metric.closedBall 0 M ∩ {X | c ≤ |X 0|}
  have hK : IsCompact K := (isCompact_closedBall 0 M).inter_right
    (isClosed_le continuous_const ((continuous_apply 0).abs))
  have hreg (X : RestartProjectionCenter) (hX : X ∈ K) :
      ContDiffAt ℝ 2 restartProjectionScaledError (0, X) := by
    apply contDiffAt_restartProjectionScaledError_shear_axis
    have H : 0 < |X 0| := hc.trans_le hX.2
    exact abs_pos.mp H
  obtain ⟨δ, hδ, C, hC, H⟩ := exists_compact_vanishing_slice_bounds hK hreg restartProjectionScaledError_axis
  refine ⟨δ, hδ, C, hC, ?_⟩
  intro X hXlo hX₀ hX₁ u hu
  have hX : X ∈ K := by
    refine ⟨?_, hXlo⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg ((abs_nonneg (X 0)).trans hX₀)).mpr
    intro i
    fin_cases i
    · exact hX₀
    · exact hX₁
  exact H X hX u hu

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_restartShearCurve (σ n₂ n₃ ρ : ℝ) :
    HasDerivAt (restartShearCurve σ n₂ n₃) (restartShearDirection σ) ρ := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [restartShearCurve, restartShearDirection] using (hasDerivAt_id ρ).const_mul σ
  · convert! hasDerivAt_const ρ n₂ using 1
  · convert! hasDerivAt_const ρ n₃ using 1

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartShearDirection_norm {σ : ℝ} (hσ : |σ| = 1) :
    ‖restartShearDirection σ‖ = 1 := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i <;> simp [restartShearDirection, hσ]
  · simpa only [restartShearDirection, Matrix.cons_val_zero, Real.norm_eq_abs, hσ] using
      norm_le_pi_norm (restartShearDirection σ) 0

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartShearCurve_annulus {a ρ σ ε n₂ n₃ : ℝ} (ha : 0 < a)
    (hρ : ρ ∈ Icc a (2 * a)) (hσ : |σ| = 1) (hε : 0 ≤ ε ∧ ε ≤ 1 / 64)
    (h₂ : 0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) (h₃ : 0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) :
    ‖restartShearCurve σ n₂ n₃ ρ‖ ≤ 2 * a ∧
      a ≤ restartRadialNorm (restartShearCurve σ n₂ n₃ ρ) ∧ |n₂ - n₃| ≤ 2 * ε * a := by
  have hρpos := ha.trans_le hρ.1
  have hsmall : 2 * ε * a ≤ 2 * a := by nlinarith only [hε.2, ha]
  refine ⟨?_, ?_, abs_le.mpr ⟨by linarith only [h₂.1, h₃.2], by linarith only [h₃.1, h₂.2]⟩⟩
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * a)).mpr
    intro i
    fin_cases i
    · change |σ * ρ| ≤ 2 * a
      simpa only [abs_mul, hσ, abs_of_pos hρpos, one_mul] using hρ.2
    · exact (show |n₂| ≤ 2 * ε * a by simpa only [abs_of_nonneg h₂.1] using h₂.2).trans hsmall
    · exact (show |n₃| ≤ 2 * ε * a by simpa only [abs_of_nonneg h₃.1] using h₃.2).trans hsmall
  · have H := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg (n₂ - n₃)) :
        (σ * ρ) ^ 2 ≤ (σ * ρ) ^ 2 + (n₂ - n₃) ^ 2)
    rw [Real.sqrt_sq_eq_abs, abs_mul, hσ, abs_of_pos hρpos, one_mul] at H
    exact hρ.1.trans H

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartReferenceRadialPhase_shear_derivative {h σ n₂ n₃ ρ a ε : ℝ}
    (hh : 0 ≤ h ∧ h ≤ 1 / 16) (ha : 0 < a) (hρ : ρ ∈ Icc a (2 * a))
    (hσ : |σ| = 1) (hε : 0 ≤ ε ∧ ε ≤ 1 / 64)
    (h₂ : 0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) (h₃ : 0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) :
    DifferentiableAt ℝ (fun x => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ x)) ρ ∧
      1 / (2 * Real.sqrt 3) ≤ deriv (fun x => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ x)) ρ ∧
      deriv (fun x => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ x)) ρ ≤ 2 / Real.sqrt 3 := by
  obtain ⟨ha0, ha1, hc0, hc1, hk0, hk1⟩ := restart_coefficients_small hh
  let A := restartShearFactor h
  let C := restartWallFactor h
  let K := restartShearCoupling h
  let d := n₂ - n₃
  have hA : 1 ≤ A ∧ A ≤ 2 := by dsimp only [A]; constructor <;> linarith only [ha0, ha1, hh.2]
  have hC : 0 ≤ C ∧ C ≤ 2 := by dsimp only [C]; constructor <;> linarith only [hc0, hc1, hh.2]
  have hK : 0 ≤ K ∧ K ≤ 1 := ⟨hk0, hk1.trans (by linarith only [hh.2])⟩
  have hP : phaseNorm (A * σ) 0 = A := by
    simp only [phaseNorm, zero_pow (by decide : 2 ≠ 0), add_zero, Real.sqrt_sq_eq_abs,
      abs_mul, abs_of_nonneg (by linarith only [hA.1] : 0 ≤ A), hσ, mul_one]
  have hQ : phaseNorm (-(K * d)) (-(C * d)) ≤ 3 * |d| := by
    have H := phaseNorm_le_abs_add (-(K * d)) (-(C * d))
    simp only [abs_neg, abs_mul, abs_of_nonneg hK.1, abs_of_nonneg hC.1] at H
    nlinarith only [H, mul_le_mul_of_nonneg_right hK.2 (abs_nonneg d),
      mul_le_mul_of_nonneg_right hC.2 (abs_nonneg d)]
  have hd : |d| ≤ 2 * ε * a := (restartShearCurve_annulus ha hρ hσ hε h₂ h₃).2.2
  have hsmall : 3 * (1 : ℝ) * phaseNorm (-(K * d)) (-(C * d)) ≤ ρ * phaseNorm (A * σ) 0 := by
    rw [hP]
    have HE := mul_le_mul_of_nonneg_right hε.2 ha.le
    have HP := mul_le_mul_of_nonneg_left hA.1 (ha.trans_le hρ.1).le
    nlinarith only [hQ, hd, HE, HP, hρ.1, ha]
  obtain ⟨v, Hv, hvlo, hvhi⟩ := hasDerivAt_phaseNorm_affine_bounds
    (by rw [hP]; linarith only [hA.1]) (ha.trans_le hρ.1) (by norm_num : (0 : ℝ) ≤ 1) hsmall
  have Href : HasDerivAt (fun x => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ x))
      (v / Real.sqrt 3) ρ := by
    convert! Hv.div_const (Real.sqrt 3) using 1
    ext x
    change Real.sqrt (restartQuadratic h (σ * x) (n₂ - n₃)) / Real.sqrt 3 = _
    dsimp only [restartQuadratic, phaseNorm, A, C, K, d]
    congr 2
    ring
  rw [hP] at hvlo hvhi
  refine ⟨Href.differentiableAt, ?_, ?_⟩ <;> rw [Href.deriv]
  · have H : (1 : ℝ) / 2 ≤ v := by linarith only [hA.1, hvlo]
    calc
      _ = (1 / 2) / Real.sqrt 3 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right H (Real.sqrt_nonneg _)
  · exact div_le_div_of_nonneg_right (hvhi.trans hA.2) (Real.sqrt_nonneg _)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartFastShearPhase_monotone :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∃ K > (0 : ℝ), ∀ q : ℝ, 2 < q → ∃ astar > (0 : ℝ),
        ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε σ n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let T := q / 2 * Real.log (1 / a)
            T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 ∧
            DifferentiableAt ℝ (restartFastShearPhase h T σ n₂ n₃) ρ ∧
            |restartFastShearPhase h T σ n₂ n₃ ρ -
              restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ ρ)| ≤ K * a ^ 2 ∧
            |deriv (restartFastShearPhase h T σ n₂ n₃) ρ -
              deriv (fun x => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ x)) ρ| ≤ K * a ∧
            1 / (4 * Real.sqrt 3) ≤ deriv (restartFastShearPhase h T σ n₂ n₃) ρ ∧
            deriv (restartFastShearPhase h T σ n₂ n₃) ρ ≤ 2 / Real.sqrt 3 + 1 := by
  obtain ⟨h₀, hh₀, H₀⟩ := exists_restartSection_radial_approximation
  refine ⟨min h₀ (1 / 16), lt_min hh₀ (by norm_num), ?_⟩
  intro h hh
  have hhsmall : 0 ≤ h ∧ h ≤ 1 / 16 := ⟨hh.1.le, hh.2.trans (min_le_right _ _)⟩
  obtain ⟨K, hK, HK⟩ := H₀ h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ 1 2 (by norm_num) (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro q hq
  obtain ⟨a₀, ha₀, Ha₀⟩ := HK q hq
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
  refine ⟨min a₀ (1 / (4 * Real.sqrt 3 * K)), lt_min ha₀ (by positivity), ?_⟩
  intro a ha ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ T
  let Z := restartShearCurve σ n₂ n₃ ρ
  have hann := restartShearCurve_annulus ha.1 hρ hσ hε h₂ h₃
  have H := Ha₀ a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ Z hann.1 (by simpa using hann.2.1)
  have Href := restartReferenceRadialPhase_shear_derivative hhsmall ha.1 hρ hσ hε h₂ h₃
  have Herr := H.2.1.hasFDerivAt.comp_hasDerivAt ρ (hasDerivAt_restartShearCurve σ n₂ n₃ ρ)
  have Hsum : HasDerivAt (restartFastShearPhase h T σ n₂ n₃)
      (fderiv ℝ (restartSectionRadialError h T) Z (restartShearDirection σ) +
        deriv (fun x => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ x)) ρ) ρ := by
    convert! Herr.add Href.1.hasDerivAt using 1
    ext x
    simp only [Function.comp_apply, Pi.add_apply, restartSectionRadialError, restartFastShearPhase,
      sub_add_cancel, T]
  have HD : |deriv (restartFastShearPhase h T σ n₂ n₃) ρ -
      deriv (fun x => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ x)) ρ| ≤ K * a := by
    rw [Hsum.deriv, add_sub_cancel_right]
    have HV := (fderiv ℝ (restartSectionRadialError h T) Z).le_opNorm (restartShearDirection σ)
    rw [restartShearDirection_norm hσ, mul_one] at HV
    exact HV.trans H.2.2.2
  have hKa : K * a ≤ 1 / (4 * Real.sqrt 3) := by
    have HB := (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3 * K)).mp
      (ha.2.trans (min_le_right _ _))
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3)).mpr
    nlinarith only [HB]
  have hquarter : 1 / (4 * Real.sqrt 3) ≤ 1 :=
    (div_le_one (by positivity : 0 < 4 * Real.sqrt 3)).mpr (by linarith only [hsqrt1])
  refine ⟨H.1, Hsum.differentiableAt, H.2.2.1, HD, ?_, ?_⟩
  · have Heq : 1 / (2 * Real.sqrt 3) = 2 * (1 / (4 * Real.sqrt 3)) := by ring
    rw [Heq] at Href
    linarith only [(abs_le.mp HD).1, Href.2.1, hKa]
  · linarith only [(abs_le.mp HD).2, Href.2.2, hKa, hquarter]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_restartSectionProjectionHeight_eq {h T : ℝ} {Z : RestartCenterState}
    (hrad : 0 < restartSectionRadicand h Z) (hT : 0 ≤ T)
    (hneg : normalizedMaxCurve (restartSectionChart h Z) 0 T 0 < 0) :
    (fun W => restartProjectionHeight (restartSectionRadialState h T W)) =ᶠ[𝓝 Z]
      (fun W => 1 + normalizedMaxCurve (restartSectionChart h W) 0 T 0) := by
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  have Hchart := (contDiffAt_restartSectionChart hrad 1).continuousAt
  have Hflow := (hasFDerivAt_normalizedMaxCurve_initial hdom).continuousAt.comp Hchart
  have Hcoord : ContinuousAt (fun W => normalizedMaxCurve (restartSectionChart h W) 0 T 0) Z :=
    (continuous_apply 0).continuousAt.comp Hflow
  have HR : ContinuousAt (restartSectionRadicand h) Z := by
    unfold restartSectionRadicand curvature
    fun_prop
  filter_upwards [HR.eventually (isOpen_Ioi.mem_nhds hrad),
    Hcoord.eventually (isOpen_Iio.mem_nhds hneg)] with W hW hN
  have HC := (normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hW.le) hT).2.1
  exact restartProjectionHeight_of_constraint HC hN

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartFastShearProjectiveEntry_bounds :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q : ℝ, 2 < q →
      ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε σ n₂ n₃ : ℝ,
        (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
        (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let T := q / 2 * Real.log (1 / a)
          let y := restartFastShearProjectiveEntry h T σ n₂ n₃ ρ
          T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 ∧
          DifferentiableAt ℝ (restartFastShearProjectiveEntry h T σ n₂ n₃) ρ ∧
          DifferentiableAt ℝ (restartFastShearHeight h T σ n₂ n₃) ρ ∧
          a ^ 2 / 4 ≤ restartFastShearHeight h T σ n₂ n₃ ρ ∧
          restartFastShearHeight h T σ n₂ n₃ ρ ≤ 6 * a ^ 2 ∧
          |deriv (restartFastShearHeight h T σ n₂ n₃) ρ| ≤ 512 * a ∧
          (1 / (8 * a) ≤ σ * y 0 ∧ σ * y 0 ≤ 18 / a) ∧
          (0 < y 1 ∧ y 1 ≤ 8 * h * a ^ (q - 2)) ∧
          (n₂ / (12 * a ^ 2) ≤ y 2 ∧ y 2 ≤ 16 * n₂ / a ^ 2) ∧
          (n₃ / (12 * a ^ 2) ≤ y 3 ∧ y 3 ≤ 16 * n₃ / a ^ 2) ∧
          (0 ≤ y 2 + y 3 ∧ y 2 + y 3 ≤ 64 * ε / a) ∧
          (0 ≤ y 2 * y 3 ∧ y 2 * y 3 ≤ 256 * n₂ * n₃ / a ^ 4) := by
  obtain ⟨C, _, h₀, hh₀, H₀⟩ := exists_restartShearFastEntry_control
  refine ⟨min h₀ 1, lt_min hh₀ (by norm_num), ?_⟩
  intro h hh q hq
  obtain ⟨astar, hastar, Ha⟩ := H₀ h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q hq
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ T y
  let Z := restartShearCurve σ n₂ n₃ ρ
  let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
  let p := restartSectionRadialState h T Z
  obtain ⟨ha1, hasmall, hT, hrad, hdom, _, hneg, Hcurve, hnpos, hnexp, hshear, hc, hv, _, hw⟩ :=
    Ha a ha ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ
  change 0 < x 2 at hnpos
  change x 2 ≤ h * a ^ q at hnexp
  change 3 * a / 4 ≤ σ * x 1 ∧ σ * x 1 ≤ 9 * a / 4 at hshear
  have hnsq : p.1 ≤ a ^ 2 := hnexp.trans (by
    have HP : a ^ q ≤ a ^ 2 := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge ha.1 ha1 hq.le
    exact (mul_le_mul_of_nonneg_left HP hh.1.le).trans
      (mul_le_of_le_one_left (sq_nonneg a) (hh.2.trans (min_le_right _ _))))
  have Hweak (i : Fin 2) : 0 ≤ p.2 i.succ ∧ p.2 i.succ ≤ a / 16 := by
    have hZi : 0 ≤ Z i.succ ∧ Z i.succ ≤ 2 * ε * a := by fin_cases i; exact h₂; exact h₃
    constructor
    · exact (div_nonneg hZi.1 (by norm_num)).trans (hw i).1
    · have H := (hw i).2.1.trans (mul_le_mul_of_nonneg_left hZi.2 (by norm_num))
      nlinarith only [H, mul_le_mul_of_nonneg_right hε.2 ha.1.le]
  have hpsmall : ‖p‖ ≤ 8 * a := by
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, abs_of_pos (show 0 < p.1 from hnpos)]
    refine ⟨hnsq.trans ?_, hc⟩
    nlinarith only [ha.1, ha1]
  obtain ⟨hd, Hlo, Hhi⟩ := restartProjectionHeight_shear_bounds
    ⟨ha.1, by linarith only [hasmall]⟩ hσ hshear ⟨hnpos.le, hnsq⟩ (Hweak 0) (Hweak 1)
  have Hgerm := (eventually_restartSectionProjectionHeight_eq hrad hT (by linarith only [hneg])).comp_tendsto
    (hasDerivAt_restartShearCurve σ n₂ n₃ ρ).continuousAt
  change (fun t => restartProjectionHeight (restartSectionRadialState h T (restartShearCurve σ n₂ n₃ t))) =ᶠ[𝓝 ρ]
    restartFastShearHeight h T σ n₂ n₃ at Hgerm
  have HD := restartProjectionHeight_derivative_bound Hcurve hd hpsmall hv
  have Hactual := HD.1.hasDerivAt.congr_of_eventuallyEq Hgerm.symm
  change a ^ 2 / 4 ≤ restartProjectionHeight p at Hlo
  change restartProjectionHeight p ≤ 6 * a ^ 2 at Hhi
  have heq : restartProjectionHeight p = 1 + x 0 := Hgerm.eq_of_nhds
  rw [heq] at Hlo Hhi
  have hA : 0 < 1 + x 0 := (by positivity [ha.1] : 0 < a ^ 2 / 4).trans_le Hlo
  have Hchart := ((contDiffAt_restartSectionChart hrad 1).differentiableAt (by norm_num)).comp ρ
    (hasDerivAt_restartShearCurve σ n₂ n₃ ρ).differentiableAt
  have HX := (hasFDerivAt_normalizedMaxCurve_initial hdom).differentiableAt.comp ρ Hchart
  have HY := ((contDiffAt_toProjectiveState 1 hA.ne').differentiableAt (by norm_num)).comp ρ HX
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by nlinarith only [hsqrt, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hsqrt2 : Real.sqrt (3 : ℝ) ≤ 2 := by nlinarith only [hsqrt, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have Hcoord (u u₀ : ℝ) (hu₀ : 0 ≤ u₀) (hu : u₀ / 2 ≤ u ∧ u ≤ 2 * u₀) :
      u₀ / (12 * a ^ 2) ≤ Real.sqrt 3 * u / (1 + x 0) ∧
        Real.sqrt 3 * u / (1 + x 0) ≤ 16 * u₀ / a ^ 2 := by
    have hu0 : 0 ≤ u := (div_nonneg hu₀ (by norm_num)).trans hu.1
    constructor
    · calc
        _ = (u₀ / 2) / (6 * a ^ 2) := by ring
        _ ≤ _ := div_le_div₀ (by positivity)
          (hu.1.trans (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt1 hu0])) hA Hhi
    · calc
        _ ≤ (4 * u₀) / (a ^ 2 / 4) := div_le_div₀ (by positivity)
          (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt2 hu0, hu.2]) (by positivity [ha.1]) Hlo
        _ = _ := by ring
  have HV := Hcoord (x 3) n₂ h₂.1 ⟨(hw 0).1, (hw 0).2.1⟩
  have HW := Hcoord (x 4) n₃ h₃.1 ⟨(hw 1).1, (hw 1).2.1⟩
  have hyV : 0 ≤ y 2 := (div_nonneg h₂.1 (by positivity)).trans HV.1
  have hyW : 0 ≤ y 3 := (div_nonneg h₃.1 (by positivity)).trans HW.1
  refine ⟨hdom, HY, Hactual.differentiableAt, Hlo, Hhi, ?_, ?_, ?_, HV, HW, ?_, ?_⟩
  · rw [Hactual.deriv]
    exact HD.2.trans (by ring_nf; rfl)
  · have heqM : σ * y 0 = Real.sqrt 3 * (σ * x 1) / (1 + x 0) := by
      change σ * (Real.sqrt 3 * x 1 / (1 + x 0)) = _
      ring
    rw [heqM]
    have hspos : 0 ≤ σ * x 1 := (by positivity [ha.1] : 0 ≤ 3 * a / 4).trans hshear.1
    constructor
    · calc
        _ = (3 * a / 4) / (6 * a ^ 2) := by field_simp; ring
        _ ≤ _ := div_le_div₀ (by positivity [ha.1])
          (hshear.1.trans (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt1 hspos])) hA Hhi
    · calc
        _ ≤ (2 * (9 * a / 4)) / (a ^ 2 / 4) := div_le_div₀ (by positivity [ha.1])
          (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt2 hspos, hshear.2]) (by positivity [ha.1]) Hlo
        _ = _ := by field_simp; ring
  · refine ⟨div_pos (mul_pos hsqrt hnpos) hA, ?_⟩
    calc
      y 1 ≤ (2 * (h * a ^ q)) / (a ^ 2 / 4) := div_le_div₀ (by positivity [hh.1, ha.1])
        (by
          change Real.sqrt 3 * x 2 ≤ 2 * (h * a ^ q)
          nlinarith only [mul_le_mul_of_nonneg_right hsqrt2 hnpos.le, hnexp]) (by positivity [ha.1]) Hlo
      _ = _ := by rw [Real.rpow_sub ha.1, Real.rpow_two]; ring
  · refine ⟨add_nonneg hyV hyW, ?_⟩
    calc
      y 2 + y 3 ≤ 16 * n₂ / a ^ 2 + 16 * n₃ / a ^ 2 := add_le_add HV.2 HW.2
      _ ≤ 16 * (2 * ε * a) / a ^ 2 + 16 * (2 * ε * a) / a ^ 2 := by gcongr; exact h₂.2; exact h₃.2
      _ = _ := by field_simp; ring
  · refine ⟨mul_nonneg hyV hyW, ?_⟩
    calc
      y 2 * y 3 ≤ (16 * n₂ / a ^ 2) * (16 * n₃ / a ^ 2) :=
        mul_le_mul HV.2 HW.2 hyW (by positivity [h₂.1])
      _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartShearFastProjectionError_bounds :
    ∃ hstar > (0 : ℝ), ∃ K > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 2 < q → 2 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε σ n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → n₃ ≤ a ^ P →
          ∀ ρ ∈ Icc a (2 * a),
            let T := q / 2 * Real.log (1 / a)
            let E := fun t => restartProjectionError (restartSectionRadialState h T (restartShearCurve σ n₂ n₃ t))
            T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 ∧
            DifferentiableAt ℝ E ρ ∧ |E ρ| ≤ K * a ^ 2 ∧ |deriv E ρ| ≤ K * a ∧
            0 < restartFastShearHeight h T σ n₂ n₃ ρ ∧
            restartFastShearProjectionPhase h T σ n₂ n₃ =ᶠ[𝓝 ρ]
              (fun t => restartProjectionPhase (restartSectionRadialState h T (restartShearCurve σ n₂ n₃ t))) := by
  obtain ⟨C, hC, hE, hhE, HE⟩ := exists_restartShearFastEntry_control
  obtain ⟨hP, hhP, HP⟩ := exists_restartFastShearProjectiveEntry_bounds
  obtain ⟨δ, hδ, B, hB, HB⟩ := exists_shearRestartProjectionScaledError_bounds (c := 3 / 4) (M := 8) (by norm_num)
  let K := B * (16 * C + 6)
  have hCpos : 0 < C := by linarith only [hC]
  have hBpos : 0 < B := by linarith only [hB]
  have hK : 0 < K := by dsimp only [K]; positivity
  have h2BK : 2 * B ≤ K := by dsimp only [K]; nlinarith only [hBpos, mul_pos hBpos hCpos]
  have hDK : B * (16 * C + 4) ≤ K := by dsimp only [K]; nlinarith only [hBpos]
  refine ⟨min hE (min hP 1), lt_min hhE (lt_min hhP (by norm_num)), K, hK, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aE, haE, HRE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q hq
  obtain ⟨aP, haP, HRP⟩ := HP h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ q hq
  refine ⟨min aE (min aP (δ / 2)), lt_min haE (lt_min haP (by positivity)), ?_⟩
  intro a ha ε σ n₂ n₃ hε hσ h₂ h₃ h₃P ρ hρ T E
  have hapos := ha.1
  let Z := restartShearCurve σ n₂ n₃ ρ
  let R := fun t => restartSectionRadialState h T (restartShearCurve σ n₂ n₃ t)
  let v := fderiv ℝ (restartSectionRadialState h T) Z (restartShearDirection σ)
  obtain ⟨ha1, _, hT, hrad, hdom, _, hneg, Hcurve, hnpos, hnexp, hs, hp, hv, hnv, hw⟩ :=
    HRE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ
  change HasDerivAt R v ρ at Hcurve
  change 0 < (R ρ).1 at hnpos
  change (R ρ).1 ≤ h * a ^ q at hnexp
  change 3 * a / 4 ≤ σ * (R ρ).2 0 ∧ σ * (R ρ).2 0 ≤ 9 * a / 4 at hs
  change ‖(R ρ).2‖ ≤ 8 * a at hp
  change ‖v‖ ≤ 2 at hv
  change |v.1| ≤ 2 * (R ρ).1 / a at hnv
  have hpower (t : ℝ) (ht : 2 < t) : a ^ t ≤ a ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge ha.1 ha1 ht.le
  have hn : (R ρ).1 ≤ a ^ 2 := hnexp.trans
    ((mul_le_mul_of_nonneg_left (hpower q hq) hh.1.le).trans
      (mul_le_of_le_one_left (sq_nonneg a) (hh.2.trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have hwpos : 0 ≤ (R ρ).2 2 := (div_nonneg h₃.1 (by norm_num)).trans (hw 1).1
  have hwall : (R ρ).2 2 ≤ 2 * a ^ 2 := (hw 1).2.1.trans
    (mul_le_mul_of_nonneg_left (h₃P.trans (hpower P hP)) (by norm_num))
  have hvwall : |v.2 2| ≤ 8 * C * (R ρ).2 2 / a := (hw 1).2.2
  let u := (restartProjectionParametersAt a (R ρ)).1
  let X := (restartProjectionParametersAt a (R ρ)).2
  let du := (restartProjectionParameterTangent a v).1
  let dX := (restartProjectionParameterTangent a v).2
  have hu : ‖u‖ ≤ 2 * a := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * a)).mpr
    intro i
    fin_cases i
    · change |a| ≤ 2 * a
      rw [abs_of_pos ha.1]
      linarith only [ha.1]
    · change |(R ρ).1 / a| ≤ 2 * a
      rw [abs_div, abs_of_pos hnpos, abs_of_pos ha.1]
      apply (div_le_iff₀ ha.1).mpr
      nlinarith only [hn, sq_nonneg a]
    · change |(R ρ).2 2 / a| ≤ 2 * a
      rw [abs_div, abs_of_nonneg hwpos, abs_of_pos ha.1]
      exact (div_le_iff₀ ha.1).mpr (by nlinarith only [hwall])
  have hXlo : 3 / 4 ≤ |X 0| := by
    change 3 / 4 ≤ |(R ρ).2 0 / a|
    rw [abs_div, abs_of_pos ha.1]
    apply (le_div_iff₀ ha.1).mpr
    have H : σ * (R ρ).2 0 ≤ |(R ρ).2 0| := by
      simpa only [abs_mul, hσ, one_mul] using le_abs_self (σ * (R ρ).2 0)
    linarith only [hs.1, H]
  have hXhi (i : Fin 2) : |X i| ≤ 8 := by
    have H (j : Fin 3) := (norm_le_pi_norm (R ρ).2 j).trans hp
    fin_cases i
    · change |(R ρ).2 0 / a| ≤ 8
      rw [abs_div, abs_of_pos ha.1]
      exact (div_le_iff₀ ha.1).mpr (H 0)
    · change |(R ρ).2 1 / a| ≤ 8
      rw [abs_div, abs_of_pos ha.1]
      exact (div_le_iff₀ ha.1).mpr (H 1)
  have Huδ : ‖u‖ ≤ δ := hu.trans (by
    linarith only [ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))])
  have H := HB X hXlo (hXhi 0) (hXhi 1) u Huδ
  have hdu : ‖du‖ ≤ 16 * C := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 16 * C)).mpr
    intro i
    fin_cases i
    · change |(0 : ℝ)| ≤ 16 * C
      rw [abs_zero]
      positivity
    · change |v.1 / a| ≤ 16 * C
      rw [abs_div, abs_of_pos ha.1]
      apply (div_le_iff₀ ha.1).mpr
      have Hn : |v.1| ≤ 2 * a := hnv.trans (by
        apply (div_le_iff₀ ha.1).mpr
        nlinarith only [hn])
      nlinarith only [Hn, mul_le_mul_of_nonneg_right hC ha.1.le, ha.1]
    · change |v.2 2 / a| ≤ 16 * C
      rw [abs_div, abs_of_pos ha.1]
      apply (div_le_iff₀ ha.1).mpr
      apply hvwall.trans
      apply (div_le_iff₀ ha.1).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hwall (by positivity : 0 ≤ 8 * C)]
  have hdX : ‖dX‖ ≤ 2 / a := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 / a)).mpr
    intro i
    have Hvc (j : Fin 3) := (norm_le_pi_norm v.2 j).trans ((norm_snd_le v).trans hv)
    fin_cases i
    · change |v.2 0 / a| ≤ 2 / a
      rw [abs_div, abs_of_pos ha.1]
      exact div_le_div_of_nonneg_right (Hvc 0) ha.1.le
    · change |v.2 1 / a| ≤ 2 / a
      rw [abs_div, abs_of_pos ha.1]
      exact div_le_div_of_nonneg_right (Hvc 1) ha.1.le
  have HD := hasDerivAt_restartProjectionError ha.1 Hcurve (H.1.differentiableAt (by norm_num))
  have HBdir := restartProjectionScaledError_direction_bound (du := du) (dX := dX) H.2.2.1 H.2.2.2
  have HAlo := (HRP a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
    ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ).2.2.2.1
  have hheight : 0 < restartFastShearHeight h T σ n₂ n₃ ρ :=
    (by positivity : 0 < a ^ 2 / 4).trans_le HAlo
  have Hgerm := (eventually_restartSectionProjectionPhase_eq_core hrad hT
    (by linarith only [hneg]) hheight).comp_tendsto (hasDerivAt_restartShearCurve σ n₂ n₃ ρ).continuousAt
  refine ⟨hdom, HD.differentiableAt, ?_, ?_, hheight, Hgerm.symm⟩
  · change |restartProjectionError (R ρ)| ≤ K * a ^ 2
    rw [restartProjectionError_rescaled ha.1, abs_mul, abs_of_pos ha.1]
    calc
      _ ≤ a * (B * ‖u‖) := mul_le_mul_of_nonneg_left H.2.1 ha.1.le
      _ ≤ a * (B * (2 * a)) := by gcongr
      _ = (2 * B) * a ^ 2 := by ring
      _ ≤ K * a ^ 2 := mul_le_mul_of_nonneg_right h2BK (sq_nonneg a)
  · change |deriv (fun t => restartProjectionError (R t)) ρ| ≤ K * a
    rw [HD.deriv, abs_mul, abs_of_pos ha.1]
    calc
      _ ≤ a * (B * ‖du‖ + B * ‖u‖ * ‖dX‖) := mul_le_mul_of_nonneg_left HBdir ha.1.le
      _ ≤ a * (B * (16 * C) + B * (2 * a) * (2 / a)) := by gcongr
      _ = (B * (16 * C + 4)) * a := by field_simp; ring
      _ ≤ K * a := mul_le_mul_of_nonneg_right hDK ha.1.le

end
end

/-- The exact reciprocal core radius has the reference shear phase and a uniformly positive ordinary derivative. -/
theorem solution :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∃ K > (0 : ℝ), ∀ q P : ℝ, 2 < q → 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε σ n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
            (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → n₃ ≤ a ^ P →
            ∀ ρ ∈ Icc a (2 * a),
              let T := q / 2 * Real.log (1 / a)
              T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 ∧
              0 < restartFastShearHeight h T σ n₂ n₃ ρ ∧
              DifferentiableAt ℝ (restartFastShearProjectionPhase h T σ n₂ n₃) ρ ∧
              |restartFastShearProjectionPhase h T σ n₂ n₃ ρ -
                restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ ρ)| ≤ K * a ^ 2 ∧
              |deriv (restartFastShearProjectionPhase h T σ n₂ n₃) ρ -
                deriv (fun t => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ t)) ρ| ≤ K * a ∧
              1 / (4 * Real.sqrt 3) ≤ deriv (restartFastShearProjectionPhase h T σ n₂ n₃) ρ ∧
              deriv (restartFastShearProjectionPhase h T σ n₂ n₃) ρ ≤ 2 / Real.sqrt 3 + 1 := by
  obtain ⟨hE, hhE, KE, hKE, HE⟩ := exists_restartShearFastProjectionError_bounds
  obtain ⟨hR, hhR, HR⟩ := exists_restartFastShearPhase_monotone
  refine ⟨min hE (min hR (1 / 16)), lt_min hhE (lt_min hhR (by norm_num)), ?_⟩
  intro h hh
  obtain ⟨KR, hKR, HKR⟩ := HR h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hhsmall : 0 ≤ h ∧ h ≤ 1 / 16 :=
    ⟨hh.1.le, hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  let K := KE + KR
  have hK : 0 < K := add_pos hKE hKR
  refine ⟨K, hK, ?_⟩
  intro q P hq hP
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aR, haR, HaR⟩ := HKR q hq
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
  refine ⟨min aE (min aR (1 / (4 * Real.sqrt 3 * K))),
    lt_min haE (lt_min haR (by positivity)), ?_⟩
  intro a ha ε σ n₂ n₃ hε hσ h₂ h₃ h₃P ρ hρ T
  let E := fun t => restartProjectionError (restartSectionRadialState h T (restartShearCurve σ n₂ n₃ t))
  obtain ⟨Hdom, HED, HEval, HEder, Hheight, Hgerm⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε σ n₂ n₃ hε hσ h₂ h₃ h₃P ρ hρ
  obtain ⟨_, HRD, HRval, HRder, _, _⟩ :=
    HaR a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
      ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ
  have Hlocal : restartFastShearProjectionPhase h T σ n₂ n₃ =ᶠ[𝓝 ρ]
      (fun t => E t + restartFastShearPhase h T σ n₂ n₃ t) := by
    filter_upwards [Hgerm] with t ht
    apply ht.trans
    change restartProjectionPhase _ =
      (restartProjectionPhase _ - restartRadialPhase _) + restartRadialPhase _
    exact (sub_add_cancel _ _).symm
  have Hsum : HasDerivAt (restartFastShearProjectionPhase h T σ n₂ n₃)
      (deriv E ρ + deriv (restartFastShearPhase h T σ n₂ n₃) ρ) ρ := by
    convert! (HED.hasDerivAt.add HRD.hasDerivAt).congr_of_eventuallyEq Hlocal using 1
  have Hval : |restartFastShearProjectionPhase h T σ n₂ n₃ ρ -
      restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ ρ)| ≤ K * a ^ 2 := by
    rw [Hlocal.eq_of_nhds, add_sub_assoc]
    calc
      _ ≤ |E ρ| + |restartFastShearPhase h T σ n₂ n₃ ρ -
          restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ ρ)| := abs_add_le _ _
      _ ≤ KE * a ^ 2 + KR * a ^ 2 := add_le_add HEval HRval
      _ = K * a ^ 2 := by dsimp only [K]; ring
  have Hder : |deriv (restartFastShearProjectionPhase h T σ n₂ n₃) ρ -
      deriv (fun t => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ t)) ρ| ≤ K * a := by
    rw [Hsum.deriv, add_sub_assoc]
    calc
      _ ≤ |deriv E ρ| + |deriv (restartFastShearPhase h T σ n₂ n₃) ρ -
          deriv (fun t => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ t)) ρ| := abs_add_le _ _
      _ ≤ KE * a + KR * a := add_le_add HEder HRder
      _ = K * a := by dsimp only [K]; ring
  have Href := restartReferenceRadialPhase_shear_derivative hhsmall ha.1 hρ hσ hε h₂ h₃
  have hKa : K * a ≤ 1 / (4 * Real.sqrt 3) := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3 * K)).mp
      (ha.2.trans ((min_le_right _ _).trans (min_le_right _ _)))
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3)).mpr
    nlinarith only [H]
  have hquarter : 1 / (4 * Real.sqrt 3) ≤ 1 :=
    (div_le_one (by positivity : 0 < 4 * Real.sqrt 3)).mpr (by linarith only [hsqrt1])
  refine ⟨Hdom, Hheight, Hsum.differentiableAt, Hval, Hder, ?_, ?_⟩
  · have heq : 1 / (2 * Real.sqrt 3) = 2 * (1 / (4 * Real.sqrt 3)) := by ring
    rw [heq] at Href
    linarith only [(abs_le.mp Hder).1, Href.2.1, hKa]
  · linarith only [(abs_le.mp Hder).2, Href.2.2, hKa, hquarter]
