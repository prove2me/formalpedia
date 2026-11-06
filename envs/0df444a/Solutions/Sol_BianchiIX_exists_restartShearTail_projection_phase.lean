-- Prove2me | solution 1 for BianchiIX.exists_restartShearTail_projection_phase
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:56:21.652339+00:00
-- url     : https://prove2.me/submissions/2e160708-900d-4be1-a8e1-e2d9d4e456ae

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_FlowTransport
import Definitions.Def_BianchiIX_ShearTransportData
import Definitions.Def_BianchiIX_RadialTransportData
import Theorems.Thm_BianchiIX_abs_sub_le_integral_bound
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiff_stateConstraint
import Theorems.Thm_BianchiIX_exists_common_rpow_budget
import Theorems.Thm_BianchiIX_exists_restartSection_radial_approximation
import Theorems.Thm_BianchiIX_exists_restartShearFastEntry_control
import Theorems.Thm_BianchiIX_exists_restartShearTail_projection_error
import Theorems.Thm_BianchiIX_exists_restartShearTail_radial_control
import Theorems.Thm_BianchiIX_hasDerivAt_normalized_components
import Theorems.Thm_BianchiIX_integral_le_of_dissipation
import Theorems.Thm_BianchiIX_le_exp_of_clock_deriv_le
import Theorems.Thm_BianchiIX_normalizedConstraintDifferential_flow
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxCurve_wall_sign
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_shearTail_constraint_bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
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
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.hasDerivAt_fderiv_apply_const {f : E → F} {gamma : ℝ → E} {v : E} {t : ℝ}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) (gamma t))
    (hg : HasDerivAt gamma v t) (w : E) :
    HasDerivAt (fun s => fderiv ℝ f (gamma s) w)
      (fderiv ℝ (fderiv ℝ f) (gamma t) v w) t := by
  have H := (hf.hasFDerivAt.comp_hasDerivAt t hg).clm_apply (hasDerivAt_const t w)
  simpa only [Function.comp_apply, ContinuousLinearMap.map_zero, add_zero] using H

end
end

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
open Set MeasureTheory

private theorem BianchiIX.integral_moments_le_of_linear_dissipation {f f' : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 < c) (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hdecay : ∀ t ∈ Icc a b, f' t ≤ -c * f t) (hfb : 0 ≤ f b) :
    (∫ t in a..b, f t) ≤ f a / c ∧ (∫ t in a..b, (t - a) * f t) ≤ f a / c ^ 2 := by
  have hcont := HasDerivAt.continuousOn hf
  refine ⟨integral_le_of_dissipation hab hc hf hcont hdecay hfb, ?_⟩
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s => (1 + c * (s - a)) * f s)
        (c * f t + (1 + c * (t - a)) * f' t) t := by
    convert! ((((hasDerivAt_id t).sub_const a).const_mul c).const_add 1).mul (hf t ht) using 1
    simp
  have H := integral_le_of_dissipation (g := fun t => (t - a) * f t) hab (sq_pos_of_pos hc) hd
    ((continuousOn_id.sub continuousOn_const).mul hcont) (fun t ht => ?_) ?_
  · simpa only [sub_self, mul_zero, add_zero, one_mul] using H
  · have hta : 0 ≤ t - a := sub_nonneg.mpr ht.1
    have hfactor : 0 ≤ 1 + c * (t - a) := by positivity
    have H' := mul_le_mul_of_nonneg_left (hdecay t ht) hfactor
    nlinarith only [H']
  · exact mul_nonneg (by positivity) hfb

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.fderiv_parameterSlice_apply {Φ : E × ℝ → F} {x : E} {t : ℝ}
    (H : DifferentiableAt ℝ Φ (x, t)) (v : E) :
    fderiv ℝ (fun y => Φ (y, t)) x v = fderiv ℝ Φ (x, t) (v, 0) := by
  have HD := H.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
  change HasFDerivAt (fun y => Φ (y, t)) _ x at HD
  rw [HD.fderiv]
  rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.curvature_abs_le_sum_sq {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    |curvature a b c| ≤ (a + b + c) ^ 2 := by
  rw [abs_le]
  constructor
  · unfold curvature
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  · unfold curvature
    nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha]

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
open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.hasDerivAt_parameter_fderiv_of_local_time {Φ G : E × ℝ → F} {x : E} {t : ℝ}
    (hΦ : ContDiffAt ℝ 2 Φ (x, t))
    (htime : (fun p => fderiv ℝ Φ p (0, 1)) =ᶠ[𝓝 (x, t)] G) (v : E) :
    HasDerivAt (fun s => fderiv ℝ (fun y => Φ (y, s)) x v)
      (fderiv ℝ (fun y => G (y, t)) x v) t := by
  have hD := (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have Htime := (hD.hasFDerivAt.clm_apply (hasFDerivAt_const (0, 1) (x, t))).congr_of_eventuallyEq htime.symm
  have hpath : HasDerivAt (fun s : ℝ => (x, s)) (0, 1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  have H := hasDerivAt_fderiv_apply_const hD hpath (v, 0)
  have Hrate : fderiv ℝ (fderiv ℝ Φ) (x, t) (0, 1) (v, 0) =
      fderiv ℝ (fun y => G (y, t)) x v := by
    rw [(hΦ.isSymmSndFDerivAt (by norm_num)).eq (0, 1) (v, 0),
      fderiv_parameterSlice_apply Htime.differentiableAt v, Htime.fderiv]
    simp
  have Hslice : (fun s => fderiv ℝ (fun y => Φ (y, s)) x v) =ᶠ[𝓝 t]
      (fun s => fderiv ℝ Φ (x, s) (v, 0)) := by
    have Hnear := (continuousAt_const.prodMk continuousAt_id).eventually
      (hΦ.eventually (by norm_num))
    filter_upwards [Hnear] with s hs
    exact fderiv_parameterSlice_apply (hs.differentiableAt (by norm_num)) v
  exact (H.congr_deriv Hrate).congr_of_eventuallyEq Hslice

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_wall_rates {a p s n x y : ℝ}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hp : p < 0)
    (hs : a / 2 ≤ s ∧ s ≤ 3 * a)
    (hn : 0 ≤ n ∧ n ≤ a ^ 2) (hx : 0 ≤ x ∧ x ≤ a ^ 2)
    (hy : 0 ≤ y ∧ y ≤ a / 16) (hc : constraint p s n x y = 1) :
    rateOne p s ≤ -2 ∧ |rateTwo p s| ≤ 6 * a ∧ rateThree p s ≤ -a / 2 := by
  obtain ⟨hQ, _, _, _, hp', hAl, hAu⟩ := shearTail_constraint_bounds ha hp hs hn hx hy hc
  have HC : p ^ 2 + s ^ 2 + curvature n x y = 1 := hc
  have ha2 : a ^ 2 ≤ a / 256 := by nlinarith only [ha.1, ha.2]
  have hs0 : 0 ≤ s := by linarith only [hs.1, ha.1]
  have hr0 := Real.sqrt_nonneg (3 : ℝ)
  have hr2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hrl : (3 : ℝ) / 2 ≤ Real.sqrt 3 := by nlinarith only [hr0, hr2]
  have hru : Real.sqrt 3 ≤ (7 : ℝ) / 4 := by nlinarith only [hr0, hr2]
  have hRslo := mul_le_mul hrl hs.1 (div_nonneg ha.1.le (by norm_num) : 0 ≤ a / 2) hr0
  have hRshi := mul_le_mul hru hs.2 hs0 (by norm_num : (0 : ℝ) ≤ 7 / 4)
  refine ⟨?_, abs_le.mpr ⟨?_, ?_⟩, ?_⟩
  · dsimp only [rateOne, shearSq]
    nlinarith only [hp', sq_nonneg (p + 15 / 16), sq_nonneg s]
  · dsimp only [rateTwo, shearSq]
    nlinarith only [HC, (abs_le.mp hQ).1, hAu, hRslo, ha2, ha.1]
  · dsimp only [rateTwo, shearSq]
    nlinarith only [HC, (abs_le.mp hQ).2, hAl, hRshi, ha2, ha.1, sq_nonneg a]
  · dsimp only [rateThree, shearSq]
    nlinarith only [HC, (abs_le.mp hQ).2, hAl, hRslo, ha2, ha.1, sq_nonneg a]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_shear_rate {a s n x y : ℝ}
    (ha : 0 ≤ a ∧ a ≤ 1 / 256) (hs : |s| ≤ 3 * a)
    (hn : 0 ≤ n) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |shearMinus s n x y| ≤ 3 * (x ^ 2 + y ^ 2 + n * (x + y) + a * n ^ 2) := by
  have hQ : |curvature n x y| ≤ n ^ 2 + x ^ 2 + y ^ 2 + 2 * n * (x + y) := by
    apply abs_le.mpr
    dsimp only [curvature]
    constructor
    · nlinarith only [sq_nonneg n, sq_nonneg (x - y)]
    · nlinarith only [mul_nonneg hx hy, mul_nonneg hn (add_nonneg hx hy)]
  have hH : |-x ^ 2 + y ^ 2 + n * x - n * y| ≤ x ^ 2 + y ^ 2 + n * (x + y) := by
    apply abs_le.mpr
    constructor <;> nlinarith only [sq_nonneg x, sq_nonneg y, mul_nonneg hn hx, mul_nonneg hn hy]
  have hr : |Real.sqrt 3| ≤ (2 : ℝ) := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have HQ := mul_le_mul hQ hs (abs_nonneg _) (by positivity : 0 ≤ n ^ 2 + x ^ 2 + y ^ 2 + 2 * n * (x + y))
  have HH := mul_le_mul hr hH (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have H := abs_add_le (curvature n x y * s) (Real.sqrt 3 * (-x ^ 2 + y ^ 2 + n * x - n * y))
  rw [abs_mul, abs_mul] at H
  have Hsmall := mul_nonneg (show 0 ≤ 1 - 6 * a by linarith only [ha.2])
    (show 0 ≤ x ^ 2 + y ^ 2 + n * (x + y) by positivity)
  dsimp only [shearMinus]
  nlinarith only [H, HQ, HH, Hsmall, mul_nonneg ha.1 (add_nonneg (sq_nonneg x) (sq_nonneg y))]

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
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.isOpen_normalizedFlowDomain (t₀ : ℝ) : IsOpen (normalizedFlowDomain t₀) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  exact mem_interior_iff_mem_nhds.mp (normalizedMaxCurve_regular hz).1

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
open Set Filter Metric
open scoped Topology ContDiff

private theorem BianchiIX.contDiffAt_normalizedMaxCurve_smooth {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    ContDiffAt ℝ ∞ (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) :=
  contDiffAt_infty.mpr (fun n => contDiffAt_normalizedMaxCurve_nat n ht)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_stateConstraint (x : NormalizedState) :
    HasFDerivAt stateConstraint (normalizedConstraintDifferential x) x :=
  ((contDiff_stateConstraint 1).differentiable (by norm_num) x).hasFDerivAt

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_constraint {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    stateConstraint (normalizedMaxCurve x t₀ t) = stateConstraint x := by
  simpa only [normalizedMaxCurve_initial] using
    normalized_constraint_constant (convex_normalizedMaxDomain x t₀)
      (fun _ hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x t₀) ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.contDiffAt_normalizedMaxCurve_two {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    ContDiffAt ℝ 2 (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) :=
  (contDiffAt_normalizedMaxCurve_smooth ht).of_le (by decide)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_shearTail_polynomials {α : ℝ → NormalizedState} {v : NormalizedState} {t : ℝ}
    (hα : HasDerivAt α v t) :
    HasDerivAt (fun u => curvature (α u 2) (α u 3) (α u 4)) (shearTailCurvatureDifferential (α t) v) t ∧
    HasDerivAt (fun u => -(α u 3) ^ 2 + (α u 4) ^ 2 + α u 2 * α u 3 - α u 2 * α u 4)
      (shearTailCouplingDifferential (α t) v) t := by
  have hn := hasDerivAt_pi.mp hα 2
  have hx := hasDerivAt_pi.mp hα 3
  have hy := hasDerivAt_pi.mp hα 4
  constructor
  · convert! (((hn.pow 2).add (hx.pow 2)).add (hy.pow 2)).sub
      ((((hn.mul hx).add (hx.mul hy)).add (hy.mul hn)).const_mul 2) using 1
    dsimp only [shearTailCurvatureDifferential]
    ring
  · convert! ((((hx.pow 2).neg.add (hy.pow 2)).add (hn.mul hx)).sub (hn.mul hy)) using 1
    dsimp only [shearTailCouplingDifferential]
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedConstraintDifferential_shearTail (z v : NormalizedState) :
    normalizedConstraintDifferential z v = 2 * z 0 * v 0 + 2 * z 1 * v 1 +
      shearTailCurvatureDifferential z v := by
  let α : ℝ → NormalizedState := fun t i => z i + t * v i
  have hα : HasDerivAt α v 0 := hasDerivAt_pi.mpr (fun i => by
    simpa only [one_mul] using ((hasDerivAt_id' (0 : ℝ)).mul_const (v i)).const_add (z i))
  have hz : α 0 = z := by ext i; simp [α]
  have H := (hasFDerivAt_stateConstraint (α 0)).comp_hasDerivAt 0 hα
  have HQ := (hasDerivAt_shearTail_polynomials hα).1
  have H' := (((hasDerivAt_pi.mp hα 0).pow 2).add ((hasDerivAt_pi.mp hα 1).pow 2)).add HQ
  change HasDerivAt (fun t => stateConstraint (α t)) _ 0 at H'
  have HE := H.unique H'
  rw [hz] at HE
  convert! HE using 1
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.le_exp_of_linear_deriv_le {I : Set ℝ} (hI : Convex ℝ I)
    {f f' : ℝ → ℝ} {c s t : ℝ}
    (hf : ∀ u ∈ I, HasDerivAt f (f' u) u) (hbound : ∀ u ∈ I, f' u ≤ c * f u)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    f t ≤ f s * Real.exp (c * (t - s)) := by
  exact le_exp_of_clock_deriv_le hI hf (fun u _ => hasDerivAt_id u)
    (fun u hu => by simpa only [mul_one] using hbound u hu) hs ht hst

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.abs_sub_le_of_deriv_primitive {f f' z z' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hb : ∀ t ∈ Icc a b, |f' t| ≤ z' t) :
    ∀ t ∈ Icc a b, |f t - f a| ≤ z t - z a := by
  intro t ht
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have HU := le_exp_of_linear_deriv_le (convex_Icc a b) (fun s hs => (hf s hs).sub (hz s hs)) (c := 0)
    (fun s hs => by nlinarith only [le_abs_self (f' s), hb s hs]) ha ht ht.1
  have HL := le_exp_of_linear_deriv_le (convex_Icc a b) (fun s hs => (hf s hs).neg.sub (hz s hs)) (c := 0)
    (fun s hs => by nlinarith only [neg_le_abs (f' s), hb s hs]) ha ht ht.1
  simp only [zero_mul, Real.exp_zero, mul_one, Pi.sub_apply, Pi.neg_apply] at HU HL
  exact abs_le.mpr ⟨by linarith only [HL], by linarith only [HU]⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_shearTailDrift {a : ℝ} (ha : a ≠ 0) (A X Y t : ℝ) :
    HasDerivAt (shearTailDrift a A X Y)
      (3 * Y ^ 2 * Real.exp (-a * t) + 3 * X ^ 2 * Real.exp (12 * a * t) +
        a * A / 4 * Real.exp (-2 * t)) t := by
  convert! (((((hasDerivAt_id' t).const_mul (-a)).exp.const_sub 1).const_mul (3 * Y ^ 2 / a)).add
    ((((hasDerivAt_id' t).const_mul (12 * a)).exp.sub_const 1).const_mul (X ^ 2 / (4 * a)))).add
      ((((hasDerivAt_id' t).const_mul (-2)).exp.const_sub 1).const_mul (a * A / 8)) using 1
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.shearTailDrift_le {a A X Y T t : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (ht : t ≤ T) :
    shearTailDrift a A X Y t ≤ 3 * Y ^ 2 / a +
      X ^ 2 / (4 * a) * Real.exp (12 * a * T) + a * A / 8 := by
  have HE := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 12 * a))
  have HX := mul_le_mul_of_nonneg_left HE (by positivity : 0 ≤ X ^ 2 / (4 * a))
  have HY : 0 ≤ 3 * Y ^ 2 / a * Real.exp (-a * t) := by positivity
  have HN : 0 ≤ a * A / 8 * Real.exp (-2 * t) := by positivity
  dsimp only [shearTailDrift]
  nlinarith only [HX, HY, HN, show 0 ≤ X ^ 2 / (4 * a) by positivity]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.shearTail_prefix {a A X Y T : ℝ} {α : ℝ → NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256)
    (hα : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt α (normalizedField (α t)) t)
    (hc : ∀ t ∈ Icc (0 : ℝ) T, stateConstraint (α t) = 1)
    (hn : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4)
    (hregion : ∀ t ∈ Icc (0 : ℝ) T, shearTailRegion a (α t))
    (hinit : α 0 2 ≤ A ∧ α 0 3 ≤ X ∧ α 0 4 ≤ Y) :
    ∀ t ∈ Icc (0 : ℝ) T,
      α t 2 ≤ A * Real.exp (-2 * t) ∧
      α t 3 ≤ X * Real.exp (6 * a * t) ∧
      α t 4 ≤ Y * Real.exp (-(a / 2) * t) ∧
      |α t 1 - α 0 1| ≤ shearTailDrift a A X Y t ∧
      a ^ 2 / 10 ≤ 1 + α t 0 ∧ 1 + α t 0 ≤ 6 * a ^ 2 ∧ α t 0 ≤ -(15 / 16) := by
  have H (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) := hregion t ht
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : α t 0 < 0 := by linarith only [(H t ht).1]
  have HB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :=
    shearTail_constraint_bounds ha (hp t ht) ⟨(H t ht).2.1, (H t ht).2.2.1⟩
      ⟨(hn t ht).1, (H t ht).2.2.2.1⟩ ⟨(hn t ht).2.1, (H t ht).2.2.2.2.1⟩
      ⟨(hn t ht).2.2, (H t ht).2.2.2.2.2⟩ (hc t ht)
  have HR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :=
    shearTail_wall_rates ha (hp t ht) ⟨(H t ht).2.1, (H t ht).2.2.1⟩
      ⟨(hn t ht).1, (H t ht).2.2.2.1⟩ ⟨(hn t ht).2.1, (H t ht).2.2.2.2.1⟩
      ⟨(hn t ht).2.2, (H t ht).2.2.2.2.2⟩ (hc t ht)
  have HW (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      α t 2 ≤ A * Real.exp (-2 * t) ∧ α t 3 ≤ X * Real.exp (6 * a * t) ∧
        α t 4 ≤ Y * Real.exp (-(a / 2) * t) := by
    have hz : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
    have HD (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) := hasDerivAt_normalized_components (hα u hu)
    have Hn := le_exp_of_linear_deriv_le (convex_Icc (0 : ℝ) T)
      (fun u hu => (HD u hu).2.2.1)
      (fun u hu => mul_le_mul_of_nonneg_right (HR u hu).1 (hn u hu).1) hz ht ht.1
    have Hx := le_exp_of_linear_deriv_le (convex_Icc (0 : ℝ) T)
      (fun u hu => (HD u hu).2.2.2.1)
      (fun u hu => mul_le_mul_of_nonneg_right ((le_abs_self _).trans (HR u hu).2.1) (hn u hu).2.1) hz ht ht.1
    have Hy := le_exp_of_linear_deriv_le (convex_Icc (0 : ℝ) T)
      (fun u hu => (HD u hu).2.2.2.2)
      (fun u hu => mul_le_mul_of_nonneg_right (HR u hu).2.2 (hn u hu).2.2) hz ht ht.1
    simp only [sub_zero] at Hn Hx Hy
    rw [neg_div] at Hy
    exact ⟨Hn.trans (mul_le_mul_of_nonneg_right hinit.1 (Real.exp_pos _).le),
      Hx.trans (mul_le_mul_of_nonneg_right hinit.2.1 (Real.exp_pos _).le),
      Hy.trans (mul_le_mul_of_nonneg_right hinit.2.2 (Real.exp_pos _).le)⟩
  have HS (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      |shearMinus (α t 1) (α t 2) (α t 3) (α t 4)| ≤
        3 * Y ^ 2 * Real.exp (-a * t) + 3 * X ^ 2 * Real.exp (12 * a * t) +
          a * A / 4 * Real.exp (-2 * t) := by
    have Hs := shearTail_shear_rate ⟨ha.1.le, ha.2⟩
      (abs_le.mpr ⟨by linarith only [(H t ht).2.1, ha.1], (H t ht).2.2.1⟩)
      (hn t ht).1 (hn t ht).2.1 (hn t ht).2.2
    have Hx := pow_le_pow_left₀ (hn t ht).2.1 (HW t ht).2.1 2
    have Hy := pow_le_pow_left₀ (hn t ht).2.2 (HW t ht).2.2 2
    have hxsq : (X * Real.exp (6 * a * t)) ^ 2 = X ^ 2 * Real.exp (12 * a * t) := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 2
      ring
    have hysq : (Y * Real.exp (-(a / 2) * t)) ^ 2 = Y ^ 2 * Real.exp (-a * t) := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 2
      ring
    rw [hxsq] at Hx
    rw [hysq] at Hy
    have ha2 : a ^ 2 ≤ a / 256 := by nlinarith only [ha.1, ha.2]
    have hcoef : 3 * (α t 3 + α t 4 + a * α t 2) ≤ a / 4 := by
      have Han := mul_le_mul_of_nonneg_left (H t ht).2.2.2.1 ha.1.le
      have Haa := mul_le_mul_of_nonneg_left ha2 ha.1.le
      nlinarith only [Han, Haa, ha2, (H t ht).2.2.2.2.1, (H t ht).2.2.2.2.2]
    have Hcoef := mul_le_mul_of_nonneg_right hcoef (hn t ht).1
    have Hn := mul_le_mul_of_nonneg_left (HW t ht).1 (div_nonneg ha.1.le (by norm_num) : 0 ≤ a / 4)
    nlinarith only [Hs, Hx, Hy, Hcoef, Hn]
  have HG := abs_sub_le_of_deriv_primitive
    (fun t ht => (hasDerivAt_normalized_components (hα t ht)).2.1)
    (fun t _ => hasDerivAt_shearTailDrift ha.1.ne' A X Y t) HS
  intro t ht
  obtain ⟨Hn, Hx, Hy⟩ := HW t ht
  obtain ⟨_, _, _, _, Hp, Hl, Hu⟩ := HB t ht
  refine ⟨Hn, Hx, Hy, ?_, Hl, Hu, Hp⟩
  simpa only [shearTailDrift, mul_zero, Real.exp_zero, sub_self, mul_zero, zero_add, sub_zero] using HG t ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.isClosed_shearTailRegion (a : ℝ) : IsClosed {z | shearTailRegion a z} :=
  (isClosed_le (continuous_apply 0) continuous_const).inter
    ((isClosed_le continuous_const (continuous_apply 1)).inter
      ((isClosed_le (continuous_apply 1) continuous_const).inter
        ((isClosed_le (continuous_apply 2) continuous_const).inter
          ((isClosed_le (continuous_apply 3) continuous_const).inter
            (isClosed_le (continuous_apply 4) continuous_const)))))

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalized_shearTail_control {a A X Y T : ℝ} {z : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hT : 0 ≤ T)
    (hA : 0 ≤ A ∧ A < a ^ 2)
    (hX : 0 ≤ X ∧ X * Real.exp (6 * a * T) < a ^ 2)
    (hY : 0 ≤ Y ∧ Y < a / 16)
    (hc : stateConstraint z = 1) (hp : z 0 < 0)
    (hs : 3 * a / 4 ≤ z 1 ∧ z 1 ≤ 9 * a / 4)
    (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hinit : z 2 ≤ A ∧ z 3 ≤ X ∧ z 4 ≤ Y) :
    ∀ t ∈ Icc (0 : ℝ) T,
      let w := normalizedMaxCurve z 0 t
      t ∈ normalizedMaxDomain z 0 ∧ shearTailRegion a w ∧
      w 2 ≤ A * Real.exp (-2 * t) ∧ w 3 ≤ X * Real.exp (6 * a * t) ∧
      w 4 ≤ Y * Real.exp (-(a / 2) * t) ∧ |w 1 - z 1| ≤ shearTailDrift a A X Y t ∧
      a ^ 2 / 10 ≤ 1 + w 0 ∧ 1 + w 0 ≤ 6 * a ^ 2 ∧ w 0 ≤ -(15 / 16) := by
  have hbudget : 3 * Y ^ 2 / a + X ^ 2 / (4 * a) * Real.exp (12 * a * T) + a * A / 8 ≤ a / 8 := by
    have HY := pow_le_pow_left₀ hY.1 hY.2.le 2
    have HX := pow_le_pow_left₀ (mul_nonneg hX.1 (Real.exp_pos _).le) hX.2.le 2
    have he : (X * Real.exp (6 * a * T)) ^ 2 = X ^ 2 * Real.exp (12 * a * T) := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 2
      ring
    rw [he] at HX
    have HA := mul_le_mul_of_nonneg_left hA.2.le (sq_nonneg a)
    have haSq : a ^ 2 ≤ 1 / 256 := by nlinarith only [ha.1, ha.2]
    have Haa := mul_nonneg (sq_nonneg a) (sub_nonneg.mpr haSq)
    have hid : a * (3 * Y ^ 2 / a + X ^ 2 / (4 * a) * Real.exp (12 * a * T) + a * A / 8) =
        3 * Y ^ 2 + X ^ 2 * Real.exp (12 * a * T) / 4 + a ^ 2 * A / 8 := by
      field_simp [ha.1.ne']
    apply (mul_le_mul_iff_right₀ ha.1).mp
    rw [hid]
    nlinarith only [HY, HX, HA, Haa, sq_nonneg a]
  let α := normalizedMaxCurve z 0
  let S := {t : ℝ | shearTailRegion a (α t)}
  have hα (t : ℝ) (ht : 0 ≤ t) : HasDerivAt α (normalizedField (α t)) t :=
    (normalizedMaxCurve_forward_of_constraint hc ht).1
  have hcon (t : ℝ) (ht : 0 ≤ t) : stateConstraint (α t) = 1 :=
    (normalizedMaxCurve_forward_of_constraint hc ht).2.1
  have hnonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4 :=
    ⟨(normalizedMaxCurve_wall_sign hc ht (0 : Fin 3)).2.mpr hn.1,
      (normalizedMaxCurve_wall_sign hc ht (1 : Fin 3)).2.mpr hn.2.1,
      (normalizedMaxCurve_wall_sign hc ht (2 : Fin 3)).2.mpr hn.2.2⟩
  have hzero : α 0 = z := normalizedMaxCurve_initial z 0
  have hXsmall : X < a ^ 2 := by
    have HE : 1 ≤ Real.exp (6 * a * T) := Real.one_le_exp_iff.mpr (by positivity [ha.1])
    exact (le_mul_of_one_le_right hX.1 HE).trans_lt hX.2
  have hsz : a / 2 ≤ z 1 ∧ z 1 ≤ 3 * a :=
    ⟨by linarith only [hs.1, ha.1], by linarith only [hs.2, ha.1]⟩
  have HB := shearTail_constraint_bounds ha hp hsz ⟨hn.1, hinit.1.trans hA.2.le⟩
    ⟨hn.2.1, hinit.2.1.trans hXsmall.le⟩ ⟨hn.2.2, hinit.2.2.trans hY.2.le⟩ hc
  have hS0 : (0 : ℝ) ∈ S := by
    change shearTailRegion a (α 0)
    rw [hzero]
    exact ⟨by linarith only [HB.2.2.2.2.1], hsz.1, hsz.2,
      hinit.1.trans hA.2.le, hinit.2.1.trans hXsmall.le, hinit.2.2.trans hY.2.le⟩
  have hclosed : IsClosed (S ∩ Icc 0 T) := by
    have H := (HasDerivAt.continuousOn (fun t (ht : t ∈ Icc (0 : ℝ) T) => hα t ht.1)).preimage_isClosed_of_isClosed
      isClosed_Icc (isClosed_shearTailRegion a)
    convert! H using 1
    ext t
    change (shearTailRegion a (α t) ∧ t ∈ Icc 0 T) ↔ (t ∈ Icc 0 T ∧ shearTailRegion a (α t))
    tauto
  have hwhole : Icc (0 : ℝ) T ⊆ S := by
    apply hclosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hS0
    intro t ht hbefore
    obtain ⟨Hn, Hx, Hy, Hs, _, _, Hp⟩ := shearTail_prefix ha
      (fun u hu => hα u hu.1) (fun u hu => hcon u hu.1) (fun u hu => hnonneg u hu.1)
      (fun u hu => hbefore hu) (by simpa only [hzero] using hinit) t ⟨ht.1, le_rfl⟩
    have HD := Hs.trans ((shearTailDrift_le ha.1 hA.1 ht.2.le).trans hbudget)
    rw [hzero] at HD
    have Hsl : a / 2 < α t 1 := by linarith only [(abs_le.mp HD).1, hs.1, ha.1]
    have Hsu : α t 1 < 3 * a := by linarith only [(abs_le.mp HD).2, hs.2, ha.1]
    have Hnn : α t 2 < a ^ 2 := Hn.trans_lt
      ((mul_le_of_le_one_right hA.1 (Real.exp_le_one_iff.mpr (by linarith only [ht.1]))).trans_lt hA.2)
    have Hxx : α t 3 < a ^ 2 := Hx.trans_lt
      ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left ht.2.le (by positivity [ha.1] : 0 ≤ 6 * a))) hX.1).trans_lt hX.2)
    have Hyy : α t 4 < a / 16 := Hy.trans_lt
      ((mul_le_of_le_one_right hY.1 (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (by linarith only [ha.1] : -(a / 2) ≤ 0) ht.1))).trans_lt hY.2)
    have Hpp : α t 0 < -(1 / 2) := by linarith only [Hp]
    have Hcont (i : Fin 5) := (continuous_apply i).continuousAt.comp (hα t ht.1).continuousAt
    have Hev : ∀ᶠ u in 𝓝 t, u ∈ S := by
      filter_upwards [(Hcont 0).eventually (isOpen_Iio.mem_nhds Hpp),
        (Hcont 1).eventually (isOpen_Ioi.mem_nhds Hsl),
        (Hcont 1).eventually (isOpen_Iio.mem_nhds Hsu),
        (Hcont 2).eventually (isOpen_Iio.mem_nhds Hnn),
        (Hcont 3).eventually (isOpen_Iio.mem_nhds Hxx),
        (Hcont 4).eventually (isOpen_Iio.mem_nhds Hyy)] with u hu0 hu1 hu2 hu3 hu4 hu5
      exact ⟨hu0.le, hu1.le, hu2.le, hu3.le, hu4.le, hu5.le⟩
    exact Hev.filter_mono nhdsWithin_le_nhds
  have H := shearTail_prefix ha
    (fun u hu => hα u hu.1) (fun u hu => hcon u hu.1) (fun u hu => hnonneg u hu.1)
    (fun u hu => hwhole hu) (by simpa only [hzero] using hinit)
  intro t ht
  refine ⟨normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1, hwhole ht, ?_⟩
  simpa only [hzero] using H t ht

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
open Set

private theorem BianchiIX.exp_shearTailTime {a : ℝ} (ha : 0 < a) (c D : ℝ) :
    Real.exp (c * a * shearTailTime a D) = a ^ (-c * D) := by
  rw [Real.rpow_def_of_pos ha]
  congr 1
  dsimp only [shearTailTime]
  rw [one_div, Real.log_inv]
  field_simp

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_shearTail_scale_control {h q D P : ℝ}
    (hh : 0 ≤ h) (hq : 2 < q) (hD : 0 ≤ D) (hP : 6 * D + 2 < P) :
    ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
      ∀ ε ζ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) → (0 ≤ ζ ∧ ζ ≤ a ^ P) →
        ∀ z : NormalizedState, stateConstraint z = 1 → z 0 < 0 →
          (3 * a / 4 ≤ z 1 ∧ z 1 ≤ 9 * a / 4) →
          (0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4) →
          (z 2 ≤ h * a ^ q ∧ z 3 ≤ 2 * ζ ∧ z 4 ≤ 4 * ε * a) →
          let T := shearTailTime a D
          0 ≤ T ∧ ∀ t ∈ Icc (0 : ℝ) T,
            let w := normalizedMaxCurve z 0 t
            t ∈ normalizedMaxDomain z 0 ∧ shearTailRegion a w ∧
            w 2 ≤ h * a ^ q * Real.exp (-2 * t) ∧
            w 3 ≤ 2 * ζ * Real.exp (6 * a * t) ∧
            w 4 ≤ 4 * ε * a * Real.exp (-(a / 2) * t) ∧
            |w 1 - z 1| ≤ 48 * ε ^ 2 * a + ζ ^ 2 / a * a ^ (-12 * D) + h * a ^ (q + 1) / 8 ∧
            a ^ 2 / 10 ≤ 1 + w 0 ∧ 1 + w 0 ≤ 6 * a ^ 2 ∧
            toProjectiveState w 2 < 1 := by
  let C : Fin 2 → ℝ := ![h, 40]
  let p : Fin 2 → ℝ := ![q - 2, P - 6 * D - 2]
  obtain ⟨astar, hastar, hastar', HB⟩ := exists_common_rpow_budget
    (C := C) (p := p) (ε := fun _ => (1 : ℝ) / 2) Finset.univ
    (fun i _ => by fin_cases i; exact hh; norm_num [C])
    (fun i _ => by fin_cases i; dsimp [p]; linarith only [hq]; dsimp [p]; linarith only [hP])
    (fun _ _ => by norm_num) (show (0 : ℝ) < 1 / 256 by norm_num)
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε ζ hε hζ z hc hp hs hn hinit T
  have haSmall : a ≤ 1 / 256 := ha.2.trans hastar'.le
  have HN : h * a ^ (q - 2) < 1 / 2 := HB a ha 0 (Finset.mem_univ _)
  have HX : 40 * a ^ (P - 6 * D - 2) < 1 / 2 := HB a ha 1 (Finset.mem_univ _)
  have hR : 0 ≤ a ^ (P - 6 * D - 2) := Real.rpow_nonneg ha.1.le _
  have hNid : h * a ^ q = (h * a ^ (q - 2)) * a ^ 2 := by
    rw [Real.rpow_sub ha.1, Real.rpow_two]
    field_simp [ha.1.ne']
  have hXid : a ^ P * a ^ (-6 * D) = a ^ (P - 6 * D - 2) * a ^ 2 := by
    rw [← Real.rpow_two a, ← Real.rpow_add ha.1, ← Real.rpow_add ha.1]
    congr 1
    ring
  have hA : 0 ≤ h * a ^ q ∧ h * a ^ q < a ^ 2 := by
    refine ⟨mul_nonneg hh (Real.rpow_nonneg ha.1.le _), ?_⟩
    rw [hNid]
    have H := mul_lt_mul_of_pos_right HN (sq_pos_of_pos ha.1)
    nlinarith only [H, sq_pos_of_pos ha.1]
  have hXtotal : 2 * ζ * Real.exp (6 * a * T) < a ^ 2 / 40 := by
    change 2 * ζ * Real.exp (6 * a * shearTailTime a D) < _
    rw [exp_shearTailTime ha.1 6 D]
    have H := mul_le_mul_of_nonneg_right hζ.2 (Real.rpow_nonneg ha.1.le (-6 * D))
    rw [hXid] at H
    have H' := mul_lt_mul_of_pos_right HX (sq_pos_of_pos ha.1)
    nlinarith only [H, H']
  have hX : 0 ≤ 2 * ζ ∧ 2 * ζ * Real.exp (6 * a * T) < a ^ 2 :=
    ⟨by linarith only [hζ.1], hXtotal.trans (by nlinarith only [sq_pos_of_pos ha.1])⟩
  have hY : 0 ≤ 4 * ε * a ∧ 4 * ε * a < a / 16 := by
    have H := mul_le_mul_of_nonneg_right hε.2 ha.1.le
    exact ⟨mul_nonneg (by linarith only [hε.1]) ha.1.le, by linarith only [H, ha.1]⟩
  have hT : 0 ≤ T := mul_nonneg (div_nonneg hD ha.1.le)
    (Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by linarith only [haSmall])))
  have H := normalized_shearTail_control ⟨ha.1, haSmall⟩ hT hA hX hY hc hp hs hn hinit
  refine ⟨hT, ?_⟩
  intro t ht w
  obtain ⟨Hdom, Hreg, Hn, Hx, Hy, Hs, HAl, HAu, _⟩ := H t ht
  have Hdrift := Hs.trans (shearTailDrift_le ha.1 hA.1 ht.2)
  have Hid : 3 * (4 * ε * a) ^ 2 / a + (2 * ζ) ^ 2 / (4 * a) * Real.exp (12 * a * T) +
      a * (h * a ^ q) / 8 = 48 * ε ^ 2 * a + ζ ^ 2 / a * a ^ (-12 * D) + h * a ^ (q + 1) / 8 := by
    change _ + _ * Real.exp (12 * a * shearTailTime a D) + _ = _
    rw [exp_shearTailTime ha.1 12 D, Real.rpow_add ha.1, Real.rpow_one]
    field_simp [ha.1.ne']
    ring
  refine ⟨Hdom, Hreg, Hn, Hx, Hy, Hdrift.trans_eq Hid, HAl, HAu, ?_⟩
  have hApos : 0 < 1 + w 0 := (div_pos (sq_pos_of_pos ha.1) (by norm_num)).trans_le HAl
  have hx0 : 0 ≤ w 3 := (normalizedMaxCurve_wall_sign hc ht.1 (1 : Fin 3)).2.mpr hn.2.1
  have hxsmall : w 3 < a ^ 2 / 40 := Hx.trans_lt
    ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ht.2 (by positivity [ha.1] : 0 ≤ 6 * a))) hX.1).trans_lt hXtotal)
  have hr : Real.sqrt (3 : ℝ) ≤ 2 := by
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  change Real.sqrt 3 * w 3 / (1 + w 0) < 1
  apply (div_lt_one hApos).mpr
  have Hr := mul_le_mul_of_nonneg_right hr hx0
  nlinarith only [Hr, hxsmall, HAl, sq_pos_of_pos ha.1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_polynomial_variation_bounds {z v : NormalizedState} {L : ℝ}
    (hL : 0 ≤ L) (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hv : |v 2| ≤ z 2 * L ∧ |v 3| ≤ z 3 * L ∧ |v 4| ≤ z 4 * L) :
    |curvature (z 2) (z 3) (z 4)| ≤ 2 * shearTailEnergy z ∧
    |shearTailCurvatureDifferential z v| ≤ 4 * shearTailEnergy z * L ∧
    |shearTailCouplingDifferential z v| ≤ 2 * shearTailEnergy z * L := by
  let M := z 2 + z 3 + z 4
  have hM : 0 ≤ M := by dsimp only [M]; positivity [hn.1, hn.2.1, hn.2.2]
  have hM2 : M ^ 2 ≤ 2 * shearTailEnergy z := by
    dsimp only [M, shearTailEnergy]
    nlinarith only [sq_nonneg (z 2), sq_nonneg (z 3 - z 4)]
  have hcoef : |z 2 - z 3 - z 4| ≤ M ∧ |z 3 - z 2 - z 4| ≤ M ∧ |z 4 - z 2 - z 3| ≤ M := by
    dsimp only [M]
    refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
      linarith only [hn.1, hn.2.1, hn.2.2]
  have HQraw : |shearTailCurvatureDifferential z v| ≤ 2 * M ^ 2 * L := by
    have H := abs_add_three ((z 2 - z 3 - z 4) * v 2) ((z 3 - z 2 - z 4) * v 3)
      ((z 4 - z 2 - z 3) * v 4)
    simp only [abs_mul] at H
    have Hn := mul_le_mul hcoef.1 hv.1 (abs_nonneg _) hM
    have Hx := mul_le_mul hcoef.2.1 hv.2.1 (abs_nonneg _) hM
    have Hy := mul_le_mul hcoef.2.2 hv.2.2 (abs_nonneg _) hM
    dsimp only [shearTailCurvatureDifferential]
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    dsimp only [M] at Hn Hx Hy ⊢
    nlinarith only [H, Hn, Hx, Hy]
  refine ⟨(curvature_abs_le_sum_sq hn.1 hn.2.1 hn.2.2).trans hM2,
    HQraw.trans (by nlinarith only [mul_le_mul_of_nonneg_right hM2 hL]), ?_⟩
  have H := abs_add_three ((z 3 - z 4) * v 2) ((z 2 - 2 * z 3) * v 3) ((2 * z 4 - z 2) * v 4)
  simp only [abs_mul] at H
  have Hn := mul_le_mul (show |z 3 - z 4| ≤ z 3 + z 4 by
    exact abs_le.mpr ⟨by linarith only [hn.2.1], by linarith only [hn.2.2]⟩)
    hv.1 (abs_nonneg _) (add_nonneg hn.2.1 hn.2.2)
  have Hx := mul_le_mul (show |z 2 - 2 * z 3| ≤ z 2 + 2 * z 3 by
    exact abs_le.mpr ⟨by linarith only [hn.1], by linarith only [hn.2.1]⟩)
    hv.2.1 (abs_nonneg _) (by positivity [hn.1, hn.2.1] : 0 ≤ z 2 + 2 * z 3)
  have Hy := mul_le_mul (show |2 * z 4 - z 2| ≤ 2 * z 4 + z 2 by
    exact abs_le.mpr ⟨by linarith only [hn.2.2], by linarith only [hn.1]⟩)
    hv.2.2 (abs_nonneg _) (by positivity [hn.1, hn.2.2] : 0 ≤ 2 * z 4 + z 2)
  dsimp only [shearTailCouplingDifferential, shearTailEnergy]
  nlinarith only [H, Hn, Hx, Hy, mul_nonneg (sq_nonneg (z 2)) hL]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_projectiveCoordinate_le {a p v B : ℝ}
    (ha : 0 < a) (hA : a ^ 2 / 10 ≤ 1 + p) (hv : 0 ≤ v ∧ v ≤ B) :
    0 ≤ projectiveCoord p v ∧ projectiveCoord p v ≤ 20 * B / a ^ 2 := by
  have hApos : 0 < 1 + p := (div_pos (sq_pos_of_pos ha) (by norm_num)).trans_le hA
  have hB : 0 ≤ B := hv.1.trans hv.2
  have hr : Real.sqrt (3 : ℝ) ≤ 2 := by
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  refine ⟨div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hv.1) hApos.le, ?_⟩
  change Real.sqrt 3 * v / (1 + p) ≤ _
  calc
    _ ≤ 2 * B / (a ^ 2 / 10) := div_le_div₀ (by positivity : 0 ≤ 2 * B)
      (mul_le_mul hr hv.2 hv.1 (by norm_num)) (by positivity) hA
    _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_projective_endpoint {a h q D ε ζ : ℝ} {z : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1) (hh : 0 ≤ h) (hD : 0 ≤ D)
    (hA : a ^ 2 / 10 ≤ 1 + z 0)
    (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hwall : z 2 ≤ h * a ^ q * Real.exp (-2 * shearTailTime a D) ∧
      z 3 ≤ 2 * ζ * Real.exp (6 * a * shearTailTime a D) ∧
      z 4 ≤ 4 * ε * a * Real.exp (-(a / 2) * shearTailTime a D)) :
    0 ≤ toProjectiveState z 1 ∧ toProjectiveState z 1 ≤ 20 * h * a ^ (q - 2) ∧
    0 ≤ toProjectiveState z 2 ∧ toProjectiveState z 2 ≤ 40 * ζ * a ^ (-6 * D - 2) ∧
    0 ≤ toProjectiveState z 3 ∧ toProjectiveState z 3 ≤ 80 * ε * a ^ (D / 2 - 1) := by
  have hT : 0 ≤ shearTailTime a D := mul_nonneg (div_nonneg hD ha.1.le)
    (Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by simpa only [one_mul] using ha.2)))
  have Hn : z 2 ≤ h * a ^ q := hwall.1.trans
    (mul_le_of_le_one_right (mul_nonneg hh (Real.rpow_nonneg ha.1.le _))
      (Real.exp_le_one_iff.mpr (by linarith only [hT])))
  have Hx := hwall.2.1
  rw [exp_shearTailTime ha.1 6 D] at Hx
  have he : Real.exp (-(a / 2) * shearTailTime a D) = a ^ (D / 2) := by
    convert! exp_shearTailTime ha.1 (-(1 / 2)) D using 1 <;> congr 1 <;> ring
  have Hy := hwall.2.2
  rw [he] at Hy
  obtain ⟨Hn0, Hn1⟩ := shearTail_projectiveCoordinate_le ha.1 hA ⟨hn.1, Hn⟩
  obtain ⟨Hx0, Hx1⟩ := shearTail_projectiveCoordinate_le ha.1 hA ⟨hn.2.1, Hx⟩
  obtain ⟨Hy0, Hy1⟩ := shearTail_projectiveCoordinate_le ha.1 hA ⟨hn.2.2, Hy⟩
  refine ⟨Hn0, Hn1.trans_eq ?_, Hx0, Hx1.trans_eq ?_, Hy0, Hy1.trans_eq ?_⟩
  · rw [Real.rpow_sub ha.1, Real.rpow_two]
    ring
  · rw [Real.rpow_sub ha.1, Real.rpow_two]
    ring
  · rw [Real.rpow_sub ha.1, Real.rpow_one]
    field_simp [ha.1.ne']
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

private theorem BianchiIX.shearTailRadius_sq (z : NormalizedState) :
    shearTailRadius z ^ 2 = z 1 ^ 2 + (z 3 - z 4) ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTailRadius_pos {z : NormalizedState} (hs : z 1 ≠ 0) : 0 < shearTailRadius z :=
  Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hs) (sq_nonneg _))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_shearTailRadius {z : NormalizedState} (hs : z 1 ≠ 0) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k shearTailRadius z := by
  have H : ContDiff ℝ k (fun z : NormalizedState => z 1 ^ 2 + (z 3 - z 4) ^ 2) := by fun_prop
  exact H.contDiffAt.sqrt (ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hs) (sq_nonneg _)))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_shearTailRadius {α : ℝ → NormalizedState} {v : NormalizedState} {r : ℝ}
    (hα : HasDerivAt α v r) (hs : α r 1 ≠ 0) :
    HasDerivAt (fun u => shearTailRadius (α u)) (shearTailRadiusDifferential (α r) v) r := by
  have H := (((hasDerivAt_pi.mp hα 1).pow 2).add
    (((hasDerivAt_pi.mp hα 3).sub (hasDerivAt_pi.mp hα 4)).pow 2)).sqrt
      (ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hs) (sq_nonneg _)))
  convert! H using 1
  change (α r 1 * v 1 + (α r 3 - α r 4) * (v 3 - v 4)) /
    Real.sqrt (α r 1 ^ 2 + (α r 3 - α r 4) ^ 2) = _
  norm_num only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTailRadius_field {z : NormalizedState} (hc : stateConstraint z = 1) (hs : z 1 ≠ 0) :
    shearTailRadiusDifferential z (normalizedField z) = shearTailRadiusRate z := by
  have hR := shearTailRadius_pos hs
  change (z 1 * shearMinus (z 1) (z 2) (z 3) (z 4) +
    (z 3 - z 4) * (rateTwo (z 0) (z 1) * z 3 - rateThree (z 0) (z 1) * z 4)) / shearTailRadius z = _
  dsimp only [shearTailRadiusRate]
  field_simp [hR.ne']
  rw [shearTailRadius_sq]
  dsimp only [stateConstraint, constraint, shearSq] at hc
  dsimp only [shearMinus, rateTwo, rateThree, shearSq]
  linear_combination -(z 3 - z 4) ^ 2 * hc

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_shearTailRadius_time {α : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t) (hc : stateConstraint (α t) = 1) (hs : α t 1 ≠ 0) :
    HasDerivAt (fun u => shearTailRadius (α u)) (shearTailRadiusRate (α t)) t :=
  (hasDerivAt_shearTailRadius hα hs).congr_deriv (shearTailRadius_field hc hs)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTailRadius_region_bounds {a : ℝ} {z : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1) (hr : shearTailRegion a z)
    (hn : 0 ≤ z 3 ∧ 0 ≤ z 4) :
    a / 2 ≤ shearTailRadius z ∧ shearTailRadius z ≤ 4 * a := by
  have hs : 0 ≤ z 1 := by linarith only [hr.2.1, ha.1]
  have ha2 : a ^ 2 ≤ a := by nlinarith only [ha.1, ha.2]
  have hd : |z 3 - z 4| ≤ 2 * a := abs_le.mpr
    ⟨by linarith only [hn.1, hr.2.2.2.2.2, ha.1],
      by linarith only [hn.2, hr.2.2.2.2.1, ha2, ha.1]⟩
  have Hs := pow_le_pow_left₀ hs hr.2.2.1 2
  have Hd := pow_le_pow_left₀ (abs_nonneg (z 3 - z 4)) hd 2
  rw [sq_abs] at Hd
  have Hsq := shearTailRadius_sq z
  have Hpos : 0 ≤ shearTailRadius z := Real.sqrt_nonneg _
  constructor
  · have Hlo := pow_le_pow_left₀ (by positivity [ha.1] : 0 ≤ a / 2) hr.2.1 2
    nlinarith only [Hlo, Hsq, Hpos, sq_nonneg (z 3 - z 4), ha.1]
  · nlinarith only [Hs, Hd, Hsq, Hpos, ha.1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTailRadius_energy_bounds {a : ℝ} {z : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1) (hr : shearTailRegion a z)
    (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4) :
    0 ≤ shearTailRadiusEnergy z ∧ shearTailRadiusEnergy z ≤ 3 * a ^ 2 ∧
    shearTailEnergy z ≤ 3 * shearTailRadiusEnergy z := by
  have ha2 : a ^ 2 ≤ a := by nlinarith only [ha.1, ha.2]
  have hx : z 3 ≤ a := hr.2.2.2.2.1.trans ha2
  have hy : z 4 ≤ a := by linarith only [hr.2.2.2.2.2, ha.1]
  have hn1 : z 2 ≤ 1 := hr.2.2.2.1.trans (ha2.trans ha.2)
  have hxy : z 3 + z 4 ≤ 2 := by linarith only [hx, hy, ha.2]
  have Hx := pow_le_pow_left₀ hn.2.1 hx 2
  have Hy := pow_le_pow_left₀ hn.2.2 hy 2
  have Hn := mul_le_mul_of_nonneg_left hn1 hn.1
  have Hxy := mul_le_mul_of_nonneg_left hxy hn.1
  dsimp only [shearTailRadiusEnergy, shearTailEnergy]
  exact ⟨by positivity [hn.1], by linarith only [Hx, Hy, hr.2.2.2.1],
    by nlinarith only [Hn, Hxy, sq_nonneg (z 3), sq_nonneg (z 4)]⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTailRadiusRate_eq_quotient (z : NormalizedState) :
    shearTailRadiusRate z = shearTailRadiusNumerator z / shearTailRadius z := by
  by_cases hR : shearTailRadius z = 0
  · simp [shearTailRadiusRate, hR]
  · dsimp only [shearTailRadiusRate, shearTailRadiusNumerator]
    field_simp
    rw [shearTailRadius_sq]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_shearTailRadiusNumerator {α : ℝ → NormalizedState} {v : NormalizedState} {r : ℝ}
    (hα : HasDerivAt α v r) :
    HasDerivAt (fun u => shearTailRadiusNumerator (α u)) (shearTailRadiusNumeratorDifferential (α r) v) r := by
  have Hp := hasDerivAt_pi.mp hα 0
  have Hs := hasDerivAt_pi.mp hα 1
  have Hn := hasDerivAt_pi.mp hα 2
  have Hd := (hasDerivAt_pi.mp hα 3).sub (hasDerivAt_pi.mp hα 4)
  have HQ := (hasDerivAt_shearTail_polynomials hα).1
  convert! ((HQ.mul ((Hs.pow 2).add (Hd.pow 2))).sub ((Hp.const_add 1).mul (Hd.pow 2))).add
    (((Hn.mul Hs).mul Hd).const_mul (Real.sqrt 3)) using 1
  · ext u
    dsimp only [shearTailRadiusNumerator, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply]
    ring
  · dsimp only [shearTailRadiusNumeratorDifferential, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply]
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_shearTailRadiusRate {α : ℝ → NormalizedState} {v : NormalizedState} {r : ℝ}
    (hα : HasDerivAt α v r) (hs : α r 1 ≠ 0) :
    HasDerivAt (fun u => shearTailRadiusRate (α u)) (shearTailRadiusRateDifferential (α r) v) r := by
  simp_rw [shearTailRadiusRate_eq_quotient]
  convert! (hasDerivAt_shearTailRadiusNumerator hα).div (hasDerivAt_shearTailRadius hα hs)
    (shearTailRadius_pos hs).ne' using 1
  dsimp only [shearTailRadiusRateDifferential]
  field_simp [(shearTailRadius_pos hs).ne']

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTailRadius_differential_bounds {a L : ℝ} {z v : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hL : 0 ≤ L) (hr : shearTailRegion a z)
    (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hv : normalizedConstraintDifferential z v = 0) (hs : |v 1| ≤ 5)
    (hw : |v 2| ≤ z 2 * L ∧ |v 3| ≤ z 3 * L ∧ |v 4| ≤ z 4 * L) :
    |shearTailRadiusDifferential z v| ≤ 40 * (1 + a * L) ∧
    |v 0| ≤ 40 * a * (1 + a * L) := by
  have ha1 : a ≤ 1 := by linarith only [ha.2]
  have ha2 : a ^ 2 ≤ a := by nlinarith only [ha.1, ha1]
  have hx : z 3 ≤ a := hr.2.2.2.2.1.trans ha2
  have hy : z 4 ≤ a := by linarith only [hr.2.2.2.2.2, ha.1]
  have hs0 : 0 < z 1 := by linarith only [hr.2.1, ha.1]
  have hR := shearTailRadius_pos hs0.ne'
  have HR := shearTailRadius_region_bounds ⟨ha.1, ha1⟩ hr hn.2
  have HE := shearTailRadius_energy_bounds ⟨ha.1, ha1⟩ hr hn
  have HQ := (shearTail_polynomial_variation_bounds hL hn hw).2.1
  have HQ' : |shearTailCurvatureDifferential z v| ≤ 36 * a ^ 2 * L := by
    have Hb : shearTailEnergy z ≤ 9 * a ^ 2 := by linarith only [HE.2.1, HE.2.2]
    have H := mul_le_mul_of_nonneg_right Hb hL
    nlinarith only [HQ, H]
  have Hd : |z 3 - z 4| ≤ 2 * a := (abs_sub _ _).trans (by
    rw [abs_of_nonneg hn.2.1, abs_of_nonneg hn.2.2]
    linarith only [hx, hy])
  have Hdv : |v 3 - v 4| ≤ 2 * a * L := by
    have H := (abs_sub (v 3) (v 4)).trans (add_le_add hw.2.1 hw.2.2)
    have Hx := mul_le_mul_of_nonneg_right hx hL
    have Hy := mul_le_mul_of_nonneg_right hy hL
    linarith only [H, Hx, Hy]
  have HS := mul_le_mul hr.2.2.1 hs (abs_nonneg _) (by positivity [ha.1] : 0 ≤ 3 * a)
  have HD := mul_le_mul Hd Hdv (abs_nonneg _) (by positivity [ha.1] : 0 ≤ 2 * a)
  have Hnum : |z 1 * v 1 + (z 3 - z 4) * (v 3 - v 4)| ≤ 15 * a + 4 * a ^ 2 * L := by
    have H := abs_add_le (z 1 * v 1) ((z 3 - z 4) * (v 3 - v 4))
    rw [abs_mul, abs_mul, abs_of_pos hs0] at H
    nlinarith only [H, HS, HD]
  constructor
  · dsimp only [shearTailRadiusDifferential]
    rw [abs_div, abs_of_pos hR]
    calc
      _ ≤ (15 * a + 4 * a ^ 2 * L) / (a / 2) := div_le_div₀
        (by positivity [ha.1]) Hnum (by positivity [ha.1]) HR.1
      _ = 30 + 8 * a * L := by field_simp [ha.1.ne']; ring
      _ ≤ _ := by nlinarith only [mul_nonneg ha.1.le hL]
  · rw [normalizedConstraintDifferential_shearTail] at hv
    have hp : z 0 < 0 := by linarith only [hr.1]
    have he : (-z 0) * v 0 = z 1 * v 1 + shearTailCurvatureDifferential z v / 2 := by nlinarith only [hv]
    have HEq := congrArg abs he
    rw [abs_mul, abs_of_pos (neg_pos.mpr hp)] at HEq
    have H := abs_add_le (z 1 * v 1) (shearTailCurvatureDifferential z v / 2)
    rw [abs_mul, abs_of_pos hs0, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at H
    have Hp := mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ) ≤ -z 0 by linarith only [hr.1]) (abs_nonneg (v 0))
    nlinarith only [HEq, H, Hp, HS, HQ', ha.1, mul_nonneg (sq_nonneg a) hL]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.shearTail_prefix_radius_moments {a T : ℝ} {α : ℝ → NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hT : 0 ≤ T)
    (hα : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt α (normalizedField (α t)) t)
    (hc : ∀ t ∈ Icc (0 : ℝ) T, stateConstraint (α t) = 1)
    (hn : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4)
    (hr : ∀ t ∈ Icc (0 : ℝ) T, shearTailRegion a (α t)) :
    (∫ t in 0..T, shearTailRadiusEnergy (α t)) ≤
      (∫ t in 0..T, shearTailEnergy (α t)) + α 0 2 / 2 ∧
    (∫ t in 0..T, t * shearTailRadiusEnergy (α t)) ≤
      (∫ t in 0..T, t * shearTailEnergy (α t)) + α 0 2 / 4 := by
  have HD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) := (hasDerivAt_normalized_components (hα t ht)).2.2.1
  have Hdec (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      rateOne (α t 0) (α t 1) * α t 2 ≤ -2 * α t 2 := by
    obtain ⟨hp, hsl, hsu, hN, hX, hY⟩ := hr t ht
    have H := (shearTail_wall_rates ha (by linarith only [hp]) ⟨hsl, hsu⟩
      ⟨(hn t ht).1, hN⟩ ⟨(hn t ht).2.1, hX⟩ ⟨(hn t ht).2.2, hY⟩ (hc t ht)).1
    exact mul_le_mul_of_nonneg_right H (hn t ht).1
  have HN := integral_moments_le_of_linear_dissipation hT (by norm_num : (0 : ℝ) < 2)
    HD Hdec (hn T ⟨hT, le_rfl⟩).1
  norm_num only [sub_zero, show (2 : ℝ) ^ 2 = 4 by norm_num] at HN
  have Hα := HasDerivAt.continuousOn hα
  have HE : ContinuousOn (fun t => shearTailRadiusEnergy (α t)) (Icc (0 : ℝ) T) := by
    unfold shearTailRadiusEnergy
    fun_prop
  have HB : ContinuousOn (fun t => shearTailEnergy (α t)) (Icc (0 : ℝ) T) := by
    unfold shearTailEnergy
    fun_prop
  have Hn : ContinuousOn (fun t => α t 2) (Icc (0 : ℝ) T) := HasDerivAt.continuousOn HD
  have Hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      shearTailRadiusEnergy (α t) ≤ shearTailEnergy (α t) + α t 2 := by
    dsimp only [shearTailRadiusEnergy, shearTailEnergy]
    nlinarith only [sq_nonneg (α t 2), mul_nonneg (hn t ht).1 (add_nonneg (hn t ht).2.1 (hn t ht).2.2)]
  constructor
  · have H := intervalIntegral.integral_mono_on (μ := volume) hT
      (HE.intervalIntegrable_of_Icc hT) ((HB.add Hn).intervalIntegrable_of_Icc hT) Hpoint
    simp only [Pi.add_apply] at H
    rw [intervalIntegral.integral_add (HB.intervalIntegrable_of_Icc hT) (Hn.intervalIntegrable_of_Icc hT)] at H
    linarith only [H, HN.1]
  · have H := intervalIntegral.integral_mono_on (μ := volume) hT
      ((continuousOn_id.mul HE).intervalIntegrable_of_Icc hT)
      (((continuousOn_id.mul HB).add (continuousOn_id.mul Hn)).intervalIntegrable_of_Icc hT)
      (fun t ht => show t * shearTailRadiusEnergy (α t) ≤ t * shearTailEnergy (α t) + t * α t 2 by
        nlinarith only [mul_le_mul_of_nonneg_left (Hpoint t ht) ht.1])
    simp only [Pi.add_apply, Pi.mul_apply, id_eq] at H
    rw [intervalIntegral.integral_add (f := fun t => t * shearTailEnergy (α t)) (g := fun t => t * α t 2)
      ((continuousOn_id.mul HB).intervalIntegrable_of_Icc hT)
      ((continuousOn_id.mul Hn).intervalIntegrable_of_Icc hT)] at H
    linarith only [H, HN.2]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTailRadius_numerator_bounds {a L : ℝ} {z v : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hL : 0 ≤ L)
    (hc : stateConstraint z = 1) (hr : shearTailRegion a z)
    (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hv : normalizedConstraintDifferential z v = 0) (hs : |v 1| ≤ 5)
    (hw : |v 2| ≤ z 2 * L ∧ |v 3| ≤ z 3 * L ∧ |v 4| ≤ z 4 * L) :
    |shearTailRadiusNumerator z| ≤ 128 * a ^ 2 * shearTailRadiusEnergy z ∧
    |shearTailRadiusNumeratorDifferential z v| ≤ 4096 * a * shearTailRadiusEnergy z * (1 + a * L) := by
  let E := shearTailRadiusEnergy z
  let B := 1 + a * L
  let d := z 3 - z 4
  let dv := v 3 - v 4
  let Q := curvature (z 2) (z 3) (z 4)
  let R := shearTailRadius z
  have ha0 : 0 ≤ a := ha.1.le
  have hn0 : 0 ≤ z 2 := hn.1
  have ha1 : a ≤ 1 := by linarith only [ha.2]
  have ha2 : a ^ 2 ≤ a := by nlinarith only [ha.1, ha1]
  have HE := shearTailRadius_energy_bounds ⟨ha.1, ha1⟩ hr hn
  have hE : 0 ≤ E := HE.1
  have hnE : z 2 ≤ E := by dsimp only [E, shearTailRadiusEnergy]; nlinarith only [sq_nonneg (z 3), sq_nonneg (z 4)]
  have hB : 0 ≤ B := by dsimp only [B]; positivity [ha.1]
  have HB1 : a * E ≤ a * E * B := by
    dsimp only [B]
    nlinarith only [mul_nonneg (mul_nonneg ha.1.le hE) (mul_nonneg ha.1.le hL)]
  have HBL : a ^ 2 * E * L ≤ a * E * B := by
    dsimp only [B]
    nlinarith only [mul_nonneg ha.1.le hE]
  have hx : z 3 ≤ a := hr.2.2.2.2.1.trans ha2
  have hy : z 4 ≤ a := by linarith only [hr.2.2.2.2.2, ha.1]
  have hs0 : 0 < z 1 := by linarith only [hr.2.1, ha.1]
  have hR : 0 < R := shearTailRadius_pos hs0.ne'
  have HR := shearTailRadius_region_bounds ⟨ha.1, ha1⟩ hr hn.2
  have HR2 : R ^ 2 ≤ 16 * a ^ 2 := by
    nlinarith only [pow_le_pow_left₀ hR.le HR.2 2]
  have HRS : z 1 ^ 2 + d ^ 2 = R ^ 2 := (shearTailRadius_sq z).symm
  have Hd : |d| ≤ 2 * a := (abs_sub _ _).trans (by
    rw [abs_of_nonneg hn.2.1, abs_of_nonneg hn.2.2]
    linarith only [hx, hy])
  have Hd2 : d ^ 2 ≤ 2 * E := by
    dsimp only [d, E, shearTailRadiusEnergy]
    nlinarith only [sq_nonneg (z 3 + z 4), hn.1]
  have Hsum2 : (z 3 + z 4) ^ 2 ≤ 2 * E := by
    dsimp only [E, shearTailRadiusEnergy]
    nlinarith only [sq_nonneg (z 3 - z 4), hn.1]
  have Hdv : |dv| ≤ (z 3 + z 4) * L := by
    have H := (abs_sub (v 3) (v 4)).trans (add_le_add hw.2.1 hw.2.2)
    dsimp only [dv]
    nlinarith only [H]
  have Hdv' : |dv| ≤ 2 * a * L := Hdv.trans (by
    have H := mul_le_mul_of_nonneg_right (show z 3 + z 4 ≤ 2 * a by linarith only [hx, hy]) hL
    exact H)
  have Hdd : |d * dv| ≤ 2 * E * L := by
    have Hdx : |d| ≤ z 3 + z 4 := by
      simpa only [d, abs_of_nonneg hn.2.1, abs_of_nonneg hn.2.2] using abs_sub (z 3) (z 4)
    rw [abs_mul]
    have H := mul_le_mul Hdx Hdv (abs_nonneg _) (add_nonneg hn.2.1 hn.2.2)
    nlinarith only [H, mul_le_mul_of_nonneg_right Hsum2 hL]
  obtain ⟨HQ, HdQ, _⟩ := shearTail_polynomial_variation_bounds hL hn hw
  have HQ' : |Q| ≤ 6 * E := by linarith only [HQ, HE.2.2]
  have HdQ' : |shearTailCurvatureDifferential z v| ≤ 12 * E * L := by
    nlinarith only [HdQ, mul_le_mul_of_nonneg_right HE.2.2 hL]
  obtain ⟨HD, Hp⟩ := shearTailRadius_differential_bounds ha hL hr hn hv hs hw
  have HD' : |z 1 * v 1 + d * dv| ≤ 160 * a * B := by
    have he : z 1 * v 1 + d * dv = R * shearTailRadiusDifferential z v := by
      dsimp only [shearTailRadiusDifferential, R, d, dv]
      field_simp [show shearTailRadius z ≠ 0 from hR.ne']
    rw [he, abs_mul, abs_of_pos hR]
    have H := mul_le_mul HR.2 HD (abs_nonneg _) (by positivity [ha.1] : 0 ≤ 4 * a)
    nlinarith only [H]
  obtain ⟨_, _, _, _, _, HAl, HAu⟩ := shearTail_constraint_bounds ha
    (by linarith only [hr.1]) ⟨hr.2.1, hr.2.2.1⟩ ⟨hn.1, hr.2.2.2.1⟩
    ⟨hn.2.1, hr.2.2.2.2.1⟩ ⟨hn.2.2, hr.2.2.2.2.2⟩ hc
  have hA : 0 ≤ 1 + z 0 := (by positivity : 0 ≤ a ^ 2 / 10).trans HAl
  have hroot : |Real.sqrt (3 : ℝ)| ≤ 2 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have Hs : |z 1| ≤ 3 * a := by rw [abs_of_pos hs0]; exact hr.2.2.1
  have V1 : |Q * (z 1 ^ 2 + d ^ 2)| ≤ 96 * a ^ 2 * E := by
    rw [HRS, abs_mul, abs_of_nonneg (sq_nonneg R)]
    have H := mul_le_mul HQ' HR2 (sq_nonneg R) (by positivity : 0 ≤ 6 * E)
    nlinarith only [H]
  have V2 : |(1 + z 0) * d ^ 2| ≤ 12 * a ^ 2 * E := by
    rw [abs_mul, abs_of_nonneg hA, abs_of_nonneg (sq_nonneg d)]
    have H := mul_le_mul HAu Hd2 (sq_nonneg d) (by positivity : 0 ≤ 6 * a ^ 2)
    nlinarith only [H]
  have V3 : |Real.sqrt 3 * z 2 * z 1 * d| ≤ 12 * a ^ 2 * E := by
    simp only [abs_mul, abs_of_nonneg hn.1]
    calc
      _ ≤ 2 * E * (3 * a) * (2 * a) := by gcongr
      _ = _ := by ring
  have VG : |shearTailRadiusNumerator z| ≤ 128 * a ^ 2 * E := by
    have H := abs_add_le (Q * (z 1 ^ 2 + d ^ 2) - (1 + z 0) * d ^ 2) (Real.sqrt 3 * z 2 * z 1 * d)
    have H' := abs_sub (Q * (z 1 ^ 2 + d ^ 2)) ((1 + z 0) * d ^ 2)
    change |Q * (z 1 ^ 2 + d ^ 2) - (1 + z 0) * d ^ 2 + Real.sqrt 3 * z 2 * z 1 * d| ≤ _
    nlinarith only [H, H', V1, V2, V3, mul_nonneg (sq_nonneg a) hE]
  have D1 : |shearTailCurvatureDifferential z v * (z 1 ^ 2 + d ^ 2)| ≤ 192 * a * E * B := by
    rw [HRS, abs_mul, abs_of_nonneg (sq_nonneg R)]
    have H := mul_le_mul HdQ' HR2 (sq_nonneg R) (by positivity : 0 ≤ 12 * E * L)
    nlinarith only [H, HBL]
  have D2 : |2 * Q * (z 1 * v 1 + d * dv)| ≤ 1920 * a * E * B := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have H := mul_le_mul HQ' HD' (abs_nonneg _) (by positivity : 0 ≤ 6 * E)
    nlinarith only [H]
  have D3 : |v 0 * d ^ 2| ≤ 80 * a * E * B := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg d)]
    have H := mul_le_mul Hp Hd2 (sq_nonneg d) (by positivity [ha.1] : 0 ≤ 40 * a * B)
    nlinarith only [H]
  have D4 : |2 * (1 + z 0) * d * dv| ≤ 24 * a * E * B := by
    rw [mul_assoc (2 * (1 + z 0)), abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hA]
    have H := mul_le_mul HAu Hdd (abs_nonneg _) (by positivity : 0 ≤ 6 * a ^ 2)
    nlinarith only [H, HBL]
  have D5 : |Real.sqrt 3 * (v 2 * z 1 * d + z 2 * v 1 * d + z 2 * z 1 * dv)| ≤ 44 * a * E * B := by
    have H1 : |v 2 * z 1 * d| ≤ 6 * a ^ 2 * E * L := by
      simp only [abs_mul]
      calc
        _ ≤ (E * L) * (3 * a) * (2 * a) := by gcongr; exact hw.1.trans (mul_le_mul_of_nonneg_right hnE hL)
        _ = _ := by ring
    have H2 : |z 2 * v 1 * d| ≤ 10 * a * E := by
      simp only [abs_mul, abs_of_nonneg hn.1]
      calc
        _ ≤ E * 5 * (2 * a) := by gcongr
        _ = _ := by ring
    have H3 : |z 2 * z 1 * dv| ≤ 6 * a ^ 2 * E * L := by
      simp only [abs_mul, abs_of_nonneg hn.1]
      calc
        _ ≤ E * (3 * a) * (2 * a * L) := by gcongr
        _ = _ := by ring
    have H := abs_add_three (v 2 * z 1 * d) (z 2 * v 1 * d) (z 2 * z 1 * dv)
    have Hsum : |v 2 * z 1 * d + z 2 * v 1 * d + z 2 * z 1 * dv| ≤ 22 * a * E * B := by
      nlinarith only [H, H1, H2, H3, HBL, HB1]
    rw [abs_mul]
    have Hprod := mul_le_mul hroot Hsum (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [Hprod]
  refine ⟨VG, ?_⟩
  let t1 := shearTailCurvatureDifferential z v * (z 1 ^ 2 + d ^ 2)
  let t2 := 2 * Q * (z 1 * v 1 + d * dv)
  let t3 := v 0 * d ^ 2
  let t4 := 2 * (1 + z 0) * d * dv
  let t5 := Real.sqrt 3 * (v 2 * z 1 * d + z 2 * v 1 * d + z 2 * z 1 * dv)
  have H := abs_add_le (t1 + t2 - t3 - t4) t5
  have H4 := abs_sub (t1 + t2 - t3) t4
  have H3 := abs_sub (t1 + t2) t3
  have H2 := abs_add_le t1 t2
  change |t1 + t2 - t3 - t4 + t5| ≤ 4096 * a * E * B
  nlinarith only [H, H4, H3, H2, D1, D2, D3, D4, D5, mul_nonneg (mul_nonneg ha.1.le hE) hB]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTailRadius_rate_bounds {a L : ℝ} {z v : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hL : 0 ≤ L)
    (hc : stateConstraint z = 1) (hr : shearTailRegion a z)
    (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hv : normalizedConstraintDifferential z v = 0) (hs : |v 1| ≤ 5)
    (hw : |v 2| ≤ z 2 * L ∧ |v 3| ≤ z 3 * L ∧ |v 4| ≤ z 4 * L) :
    |shearTailRadiusRate z| ≤ 256 * a * shearTailRadiusEnergy z ∧
    |shearTailRadiusRateDifferential z v| ≤ 32768 * shearTailRadiusEnergy z * (1 + a * L) := by
  let E := shearTailRadiusEnergy z
  let B := 1 + a * L
  have hE : 0 ≤ E := by dsimp only [E, shearTailRadiusEnergy]; positivity [hn.1]
  have hB : 0 ≤ B := by dsimp only [B]; positivity [ha.1]
  have hs0 : 0 < z 1 := by linarith only [hr.2.1, ha.1]
  have hR := shearTailRadius_pos hs0.ne'
  have HR := shearTailRadius_region_bounds ⟨ha.1, by linarith only [ha.2]⟩ hr hn.2
  obtain ⟨HG, HDG⟩ := shearTailRadius_numerator_bounds ha hL hc hr hn hv hs hw
  have HD := (shearTailRadius_differential_bounds ha hL hr hn hv hs hw).1
  constructor
  · rw [shearTailRadiusRate_eq_quotient, abs_div, abs_of_pos hR]
    calc
      _ ≤ (128 * a ^ 2 * E) / (a / 2) := div_le_div₀ (by positivity) HG (by positivity [ha.1]) HR.1
      _ = _ := by field_simp [ha.1.ne']; ring
  · have H1 : |shearTailRadiusNumeratorDifferential z v / shearTailRadius z| ≤ 8192 * E * B := by
      rw [abs_div, abs_of_pos hR]
      calc
        _ ≤ (4096 * a * E * B) / (a / 2) := div_le_div₀ (by positivity [ha.1]) HDG (by positivity [ha.1]) HR.1
        _ = _ := by field_simp [ha.1.ne']; ring
    have H2 : |shearTailRadiusNumerator z * shearTailRadiusDifferential z v / shearTailRadius z ^ 2| ≤ 20480 * E * B := by
      rw [abs_div, abs_mul, abs_of_pos (sq_pos_of_pos hR)]
      calc
        _ ≤ ((128 * a ^ 2 * E) * (40 * B)) / (a / 2) ^ 2 := div_le_div₀
          (by positivity) (mul_le_mul HG HD (abs_nonneg _) (by positivity))
          (by positivity [ha.1]) (pow_le_pow_left₀ (by positivity [ha.1]) HR.1 2)
        _ = _ := by field_simp [ha.1.ne']; ring
    have H := abs_sub (shearTailRadiusNumeratorDifferential z v / shearTailRadius z)
      (shearTailRadiusNumerator z * shearTailRadiusDifferential z v / shearTailRadius z ^ 2)
    dsimp only [shearTailRadiusRateDifferential]
    nlinarith only [H, H1, H2, mul_nonneg hE hB]

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
open Set

private theorem BianchiIX.exists_restartShearTail_control :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 2 < q → 0 ≤ D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε ζ ν : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 ≤ ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 ≤ ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let Z := restartShearCurve 1 ζ ν ρ
            let t₀ := q / 2 * Real.log (1 / a)
            let T := shearTailTime a D
            let x := restartSectionChart h Z
            let y := normalizedMaxCurve x 0 t₀
            a ≤ 1 ∧ 0 ≤ t₀ ∧ 0 ≤ T ∧ 0 < restartSectionRadicand h Z ∧ stateConstraint x = 1 ∧
            (∀ t ∈ Icc (0 : ℝ) T,
              let w := restartShearTailFlow h a q ζ ν t ρ
              t + t₀ ∈ normalizedMaxDomain x 0 ∧ w = normalizedMaxCurve y 0 t ∧
              stateConstraint w = 1 ∧ (0 ≤ w 2 ∧ 0 ≤ w 3 ∧ 0 ≤ w 4) ∧
              shearTailRegion a w ∧ w 2 ≤ h * a ^ q * Real.exp (-2 * t) ∧
              w 3 ≤ 2 * ζ * Real.exp (6 * a * t) ∧
              w 4 ≤ 4 * ε * a * Real.exp (-(a / 2) * t) ∧
              |w 1 - y 1| ≤ 48 * ε ^ 2 * a + ζ ^ 2 / a * a ^ (-12 * D) + h * a ^ (q + 1) / 8 ∧
              a ^ 2 / 10 ≤ 1 + w 0 ∧ 1 + w 0 ≤ 6 * a ^ 2 ∧ toProjectiveState w 2 < 1) ∧
            (let w := restartShearTailFlow h a q ζ ν T ρ;
              toProjectiveState w 1 ≤ 20 * h * a ^ (q - 2) ∧
              toProjectiveState w 2 ≤ 40 * ζ * a ^ (-6 * D - 2) ∧
              toProjectiveState w 3 ≤ 80 * ε * a ^ (D / 2 - 1)) := by
  obtain ⟨C, _, hstar, hhstar, HF⟩ := exists_restartShearFastEntry_control
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aF, haF, HFa⟩ := HF h hh q hq
  obtain ⟨aT, haT, HTa⟩ := exists_shearTail_scale_control hh.1.le hq hD hP
  refine ⟨min aF aT, lt_min haF haT, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ Z t₀ T x y
  have hε' : 0 ≤ ε ∧ ε ≤ 1 / 64 := ⟨hε.1, by linarith only [hε.2]⟩
  obtain ⟨ha1, _, ht₀, hrad, hdom, hcy, hpy, _, hnpos, hnhi, hsy, _, _, _, HW⟩ :=
    HFa a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε 1 ζ ν hε' (by norm_num)
      ⟨hζ.1, hζ.2.2⟩ hν ρ hρ
  have hcx : stateConstraint x = 1 := restartSectionChart_constraint hrad.le
  have Hn : 0 ≤ y 2 ∧ y 2 ≤ h * a ^ q := ⟨hnpos.le, hnhi⟩
  have Hx : 0 ≤ y 3 ∧ y 3 ≤ 2 * ζ := by
    have H := HW 0
    change ζ / 2 ≤ y 3 ∧ y 3 ≤ 2 * ζ ∧ _ at H
    exact ⟨by linarith only [H.1, hζ.1], H.2.1⟩
  have Hy : 0 ≤ y 4 ∧ y 4 ≤ 4 * ε * a := by
    have H := HW 1
    change ν / 2 ≤ y 4 ∧ y 4 ≤ 2 * ν ∧ _ at H
    exact ⟨by linarith only [H.1, hν.1], by linarith only [H.2.1, hν.2]⟩
  have HS : 3 * a / 4 ≤ y 1 ∧ y 1 ≤ 9 * a / 4 := by
    change 3 * a / 4 ≤ 1 * y 1 ∧ 1 * y 1 ≤ 9 * a / 4 at hsy
    simpa only [one_mul] using hsy
  obtain ⟨hT, HT⟩ := HTa a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ hε
    ⟨hζ.1, hζ.2.1⟩ y hcy (by linarith only [hpy]) HS ⟨Hn.1, Hx.1, Hy.1⟩ ⟨Hn.2, Hx.2, Hy.2⟩
  have Hall (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      t + t₀ ∈ normalizedMaxDomain x 0 ∧
      restartShearTailFlow h a q ζ ν t ρ = normalizedMaxCurve y 0 t ∧
      stateConstraint (restartShearTailFlow h a q ζ ν t ρ) = 1 ∧
      (0 ≤ restartShearTailFlow h a q ζ ν t ρ 2 ∧
        0 ≤ restartShearTailFlow h a q ζ ν t ρ 3 ∧ 0 ≤ restartShearTailFlow h a q ζ ν t ρ 4) := by
    have htime : 0 ≤ t + t₀ := add_nonneg ht.1 ht₀
    have htot := normalizedMaxDomain_contains_Ici_of_constraint hcx 0 htime
    have Heq : restartShearTailFlow h a q ζ ν t ρ = normalizedMaxCurve y 0 t := by
      change normalizedMaxCurve x 0 (t + t₀) = normalizedMaxCurve (normalizedMaxCurve x 0 t₀) 0 t
      simpa only [zero_add] using
        (normalizedMaxCurve_shift (by simpa only [zero_add] using hdom) htot).symm
    refine ⟨htot, Heq, (normalizedMaxCurve_forward_of_constraint hcx htime).2.1, ?_⟩
    rw [Heq]
    exact ⟨(normalizedMaxCurve_wall_sign hcy ht.1 (0 : Fin 3)).2.mpr Hn.1,
      (normalizedMaxCurve_wall_sign hcy ht.1 (1 : Fin 3)).2.mpr Hx.1,
      (normalizedMaxCurve_wall_sign hcy ht.1 (2 : Fin 3)).2.mpr Hy.1⟩
  refine ⟨ha1, ht₀, hT, hrad, hcx, ?_, ?_⟩
  · intro t ht w
    obtain ⟨Hdom, Heq, Hc, Hpos⟩ := Hall t ht
    refine ⟨Hdom, Heq, Hc, Hpos, ?_⟩
    change w = normalizedMaxCurve y 0 t at Heq
    rw [Heq]
    exact (HT t ht).2
  · have heq := (Hall T ⟨hT, le_rfl⟩).2.1
    obtain ⟨_, _, HnT, HxT, HyT, _, HAl, _, _⟩ := HT T ⟨hT, le_rfl⟩
    have Hpos := (Hall T ⟨hT, le_rfl⟩).2.2.2
    rw [heq] at Hpos ⊢
    have Hproj := shearTail_projective_endpoint ⟨ha.1, ha1⟩ hh.1.le hD HAl Hpos ⟨HnT, HxT, HyT⟩
    exact ⟨Hproj.2.1, Hproj.2.2.2.1, Hproj.2.2.2.2.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartShearInitialVariation_tangent {h ζ ν ρ : ℝ}
    (hrad : 0 < restartSectionRadicand h (restartShearCurve 1 ζ ν ρ)) :
    HasDerivAt (fun r => restartSectionChart h (restartShearCurve 1 ζ ν r))
      (restartShearInitialVariation h ζ ν ρ) ρ ∧
    normalizedConstraintDifferential (restartSectionChart h (restartShearCurve 1 ζ ν ρ))
      (restartShearInitialVariation h ζ ν ρ) = 0 := by
  have HD := ((contDiffAt_restartSectionChart hrad 1).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
    ρ (hasDerivAt_restartShearCurve 1 ζ ν ρ)
  refine ⟨HD, ?_⟩
  have HR : Continuous (fun r => restartSectionRadicand h (restartShearCurve 1 ζ ν r)) := by
    unfold restartSectionRadicand restartShearCurve curvature
    fun_prop
  have HE : (fun r => stateConstraint (restartSectionChart h (restartShearCurve 1 ζ ν r))) =ᶠ[𝓝 ρ]
      fun _ => (1 : ℝ) := by
    filter_upwards [HR.continuousAt.eventually (isOpen_Ioi.mem_nhds hrad)] with r hr
    exact restartSectionChart_constraint hr.le
  exact ((hasFDerivAt_stateConstraint _).comp_hasDerivAt ρ HD).unique
    ((hasDerivAt_const ρ (1 : ℝ)).congr_of_eventuallyEq HE)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartShearTailFlow {h a q ζ ν t ρ : ℝ}
    (hrad : 0 < restartSectionRadicand h (restartShearCurve 1 ζ ν ρ))
    (ht : t + q / 2 * Real.log (1 / a) ∈
      normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0) :
    HasDerivAt (restartShearTailFlow h a q ζ ν t) (restartShearTailRadialVariation h a q ζ ν t ρ) ρ := by
  exact (hasFDerivAt_normalizedMaxCurve_initial ht).comp_hasDerivAt ρ
    (restartShearInitialVariation_tangent hrad).1

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartShearTailRadius_variation {h a q ζ ν t ρ : ℝ}
    (hrad : 0 < restartSectionRadicand h (restartShearCurve 1 ζ ν ρ))
    (ht : t + q / 2 * Real.log (1 / a) ∈
      normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0)
    (hs : restartShearTailFlow h a q ζ ν t ρ 1 ≠ 0) :
    HasDerivAt (fun u => deriv (fun r => shearTailRadius (restartShearTailFlow h a q ζ ν u r)) ρ)
      (shearTailRadiusRateDifferential (restartShearTailFlow h a q ζ ν t ρ)
        (restartShearTailRadialVariation h a q ζ ν t ρ)) t := by
  let t₀ := q / 2 * Real.log (1 / a)
  let X : ℝ × ℝ → NormalizedState := fun p => restartShearTailFlow h a q ζ ν p.2 p.1
  let Φ : ℝ × ℝ → ℝ := fun p => shearTailRadius (X p)
  let G : ℝ × ℝ → ℝ := fun p => shearTailRadiusRate (X p)
  have HC : ContDiff ℝ 2 (restartShearCurve 1 ζ ν) := by
    rw [contDiff_pi]
    intro i
    fin_cases i <;> dsimp [restartShearCurve] <;> fun_prop
  have Hchart := (contDiffAt_restartSectionChart hrad 2).comp (ρ, t)
    (HC.contDiffAt.comp (ρ, t) contDiffAt_fst)
  have Hclock : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => p.2 + t₀) (ρ, t) := by fun_prop
  have HI := Hchart.prodMk Hclock
  have HX : ContDiffAt ℝ 2 X (ρ, t) := (contDiffAt_normalizedMaxCurve_two ht).comp (ρ, t)
    (g := fun y : NormalizedState × ℝ => normalizedMaxCurve y.1 0 y.2) HI
  have HΦ : ContDiffAt ℝ 2 Φ (ρ, t) :=
    (contDiffAt_shearTailRadius hs 2).comp (ρ, t) (g := shearTailRadius) HX
  have Hrad : Continuous (fun p : ℝ × ℝ => restartSectionRadicand h (restartShearCurve 1 ζ ν p.1)) := by
    unfold restartSectionRadicand restartShearCurve curvature
    fun_prop
  have Htime : (fun p => fderiv ℝ Φ p (0, 1)) =ᶠ[𝓝 (ρ, t)] G := by
    filter_upwards [Hrad.continuousAt.eventually (isOpen_Ioi.mem_nhds hrad),
      HI.continuousAt.eventually ((isOpen_normalizedFlowDomain 0).mem_nhds ht),
      ((continuous_apply 1).continuousAt.comp HX.continuousAt).eventually_ne hs,
      HΦ.eventually (by norm_num)] with p hp ht' hs' hΦ
    have HD : HasDerivAt (fun u => X (p.1, u)) (normalizedField (X p)) p.2 := by
      have H := (hasDerivAt_normalizedMaxCurve ht').scomp p.2 ((hasDerivAt_id' p.2).add_const t₀)
      simpa only [Function.comp_def, one_smul, X, restartShearTailFlow, t₀] using H
    have Hcon : stateConstraint (X p) = 1 :=
      (normalizedMaxCurve_constraint ht').trans (restartSectionChart_constraint hp.le)
    have HR := hasDerivAt_shearTailRadius_time HD Hcon hs'
    have HP := (hΦ.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id' p.2))
    exact HP.unique HR
  have HM := hasDerivAt_parameter_fderiv_of_local_time HΦ Htime (1 : ℝ)
  have HR := hasDerivAt_shearTailRadiusRate (hasDerivAt_restartShearTailFlow hrad ht) hs
  change HasDerivAt (fun u => deriv (fun r => shearTailRadius (restartShearTailFlow h a q ζ ν u r)) ρ)
    (deriv (fun r => shearTailRadiusRate (restartShearTailFlow h a q ζ ν t r)) ρ) t at HM
  rwa [HR.deriv] at HM

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.exists_restartShearTail_radius_rates :
    ∃ C ≥ (32 : ℝ), ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 2 < q → 0 ≤ D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε ζ ν : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let T := shearTailTime a D
            let α := fun t => restartShearTailFlow h a q ζ ν t ρ
            let v := fun t => restartShearTailRadialVariation h a q ζ ν t ρ
            let L₀ := shearTailLogSize (α 0) (v 0)
            a ≤ 1 / 256 ∧ 0 ≤ T ∧ L₀ ≤ 2 + 4 * C * q * |Real.log a| ∧
            ContinuousOn (fun t => shearTailRadiusEnergy (α t)) (Icc (0 : ℝ) T) ∧
            (∫ t in 0..T, shearTailRadiusEnergy (α t)) ≤ 5 * a ∧
            (∫ t in 0..T, t * shearTailRadiusEnergy (α t)) ≤ 1 / 256 + (3 + D) * a ∧
            ∀ t ∈ Icc (0 : ℝ) T,
              a / 2 ≤ shearTailRadius (α t) ∧ shearTailRadius (α t) ≤ 4 * a ∧
              HasDerivAt (fun r => shearTailRadius (restartShearTailFlow h a q ζ ν t r))
                (shearTailRadiusDifferential (α t) (v t)) ρ ∧
              HasDerivAt (fun u => shearTailRadius (α u)) (shearTailRadiusRate (α t)) t ∧
              HasDerivAt (fun r => shearTailRadiusRate (restartShearTailFlow h a q ζ ν t r))
                (shearTailRadiusRateDifferential (α t) (v t)) ρ ∧
              HasDerivAt (fun u => deriv (fun r => shearTailRadius (restartShearTailFlow h a q ζ ν u r)) ρ)
                (shearTailRadiusRateDifferential (α t) (v t)) t ∧
              |shearTailRadiusRate (α t)| ≤ 256 * a * shearTailRadiusEnergy (α t) ∧
              |shearTailRadiusRateDifferential (α t) (v t)| ≤
                32768 * shearTailRadiusEnergy (α t) * (1 + 2 * a * L₀ + 20 * a * t) := by
  obtain ⟨C, hC, hR, hhR, HR⟩ := exists_restartShearTail_radial_control
  obtain ⟨hV, hhV, HV⟩ := exists_restartShearTail_control
  refine ⟨C, hC, min hR hV, lt_min hhR hhV, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aR, haR, HRa⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aV, haV, HVa⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq hD hP
  refine ⟨min aR aV, lt_min haR haV, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ T α v L₀
  obtain ⟨hasmall, hT, HL₀, HJ₀, HJ₁, _, _, _, HRt⟩ :=
    HRa a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, _, hrad, _, HT, _⟩ :=
    HVa a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  have Hα (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt α (normalizedField (α t)) t := by
    have H := (hasDerivAt_normalizedMaxCurve (HT t ht).1).scomp t
      ((hasDerivAt_id' t).add_const (q / 2 * Real.log (1 / a)))
    simpa only [Function.comp_def, one_smul, α, restartShearTailFlow] using H
  have HM := shearTail_prefix_radius_moments ⟨ha.1, hasmall⟩ hT Hα
    (fun t ht => (HT t ht).2.2.1) (fun t ht => (HT t ht).2.2.2.1)
    (fun t ht => (HT t ht).2.2.2.2.1)
  have Hcont := HasDerivAt.continuousOn Hα
  have HEcont : ContinuousOn (fun t => shearTailRadiusEnergy (α t)) (Icc (0 : ℝ) T) := by
    unfold shearTailRadiusEnergy
    fun_prop
  have Hreg₀ : shearTailRegion a (α 0) := (HT 0 ⟨le_rfl, hT⟩).2.2.2.2.1
  have ha2 : a ^ 2 ≤ a := by nlinarith only [ha.1, hasmall]
  have HI₀ : (∫ t in 0..T, shearTailRadiusEnergy (α t)) ≤ 5 * a := by
    linarith only [HM.1, HJ₀, Hreg₀.2.2.2.1, ha2, ha.1]
  have HI₁ : (∫ t in 0..T, t * shearTailRadiusEnergy (α t)) ≤ 1 / 256 + (3 + D) * a := by
    nlinarith only [HM.2, HJ₁, Hreg₀.2.2.2.1, ha2, ha.1]
  refine ⟨hasmall, hT, HL₀, HEcont, HI₀, HI₁, ?_⟩
  intro t ht
  obtain ⟨Hderiv, Hpos, HS, HL, _⟩ := HRt t ht
  have Hcon : stateConstraint (α t) = 1 := (HT t ht).2.2.1
  have Hnon : 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4 := (HT t ht).2.2.2.1
  have Hreg : shearTailRegion a (α t) := (HT t ht).2.2.2.2.1
  have hs : α t 1 ≠ 0 := ne_of_gt (by linarith only [Hreg.2.1, ha.1])
  have Hbounds := shearTailRadius_region_bounds ⟨ha.1, by linarith only [hasmall]⟩ Hreg Hnon.2
  have HD := Hα t ht
  have Hv : normalizedConstraintDifferential (α t) (v t) = 0 := by
    have H := congrArg (fun L : NormalizedState →L[ℝ] ℝ => L (restartShearInitialVariation h ζ ν ρ))
      (normalizedConstraintDifferential_flow (HT t ht).1)
    simp only [ContinuousLinearMap.comp_apply] at H
    exact H.trans (restartShearInitialVariation_tangent hrad).2
  have HW (i : Fin 3) (hi : 0 < α t (i.addNat 2)) :
      |v t (i.addNat 2)| ≤ α t (i.addNat 2) * shearTailLogSize (α t) (v t) := by
    have H := norm_le_pi_norm (fun j : Fin 3 => v t (j.addNat 2) / α t (j.addNat 2)) i
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hi] at H
    simpa only [shearTailLogSize, mul_comm] using (div_le_iff₀ hi).mp H
  have HB := shearTailRadius_rate_bounds ⟨ha.1, hasmall⟩ (norm_nonneg _) Hcon Hreg Hnon Hv HS
    ⟨HW 0 Hpos.1, HW 1 Hpos.2.1, HW 2 Hpos.2.2⟩
  refine ⟨Hbounds.1, Hbounds.2, hasDerivAt_shearTailRadius Hderiv hs,
    hasDerivAt_shearTailRadius_time HD Hcon hs, hasDerivAt_shearTailRadiusRate Hderiv hs,
    hasDerivAt_restartShearTailRadius_variation hrad (HT t ht).1 hs, HB.1, ?_⟩
  have HE : 0 ≤ shearTailRadiusEnergy (α t) := by dsimp only [shearTailRadiusEnergy]; positivity [Hnon.1]
  have H := mul_le_mul_of_nonneg_left HL
    (by positivity [ha.1] : 0 ≤ 32768 * a * shearTailRadiusEnergy (α t))
  have Hrate : |shearTailRadiusRateDifferential (α t) (v t)| ≤
      32768 * shearTailRadiusEnergy (α t) * (1 + a * shearTailLogSize (α t) (v t)) := HB.2
  nlinarith only [Hrate, H]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exists_restartShearTail_radius_transfer :
    ∃ C ≥ (32 : ℝ), ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 2 < q → 0 ≤ D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε ζ ν : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let T := shearTailTime a D
            let F := fun r => shearTailRadius (restartShearTailFlow h a q ζ ν T r) -
              shearTailRadius (restartShearTailFlow h a q ζ ν 0 r)
            DifferentiableAt ℝ F ρ ∧
            |F ρ| + a * |deriv F ρ| ≤ (1280 + 32768 * (105 + 40 * C * q + 20 * D)) * a ^ 2 := by
  obtain ⟨C, hC, hstar, hhstar, H⟩ := exists_restartShearTail_radius_rates
  refine ⟨C, hC, hstar, hhstar, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨astar, hastar, HA⟩ := H h hh q D P hq hD hP
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ T F
  let α := fun t => restartShearTailFlow h a q ζ ν t ρ
  let v := fun t => restartShearTailRadialVariation h a q ζ ν t ρ
  let L₀ := shearTailLogSize (α 0) (v 0)
  let E := fun t => shearTailRadiusEnergy (α t)
  let I₀ := ∫ t in 0..T, E t
  let I₁ := ∫ t in 0..T, t * E t
  obtain ⟨hasmall, hT, HL₀, HE, HI₀, HI₁, HT⟩ := HA a ha ε ζ ν hε hζ hν ρ hρ
  have ha1 : a ≤ 1 := by linarith only [hasmall]
  have HC : 0 ≤ C := by linarith only [hC]
  have HQ : 0 ≤ q := by linarith only [hq]
  have HL₀0 : 0 ≤ L₀ := norm_nonneg _
  have hlog : a * |Real.log a| ≤ 1 := by
    have H := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos ha.1) ha.1.le
    rw [mul_sub, mul_one, mul_inv_cancel₀ ha.1.ne'] at H
    rw [abs_of_nonpos (Real.log_nonpos ha.1.le ha1)]
    nlinarith only [H, ha.1]
  have HL : a * L₀ ≤ 2 + 4 * C * q := by
    have H := mul_le_mul_of_nonneg_left HL₀ ha.1.le
    have Hlog := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 4 * C * q)
    nlinarith only [H, Hlog, ha1]
  have HI₁' : I₁ ≤ 4 + D := by
    have H := mul_le_mul_of_nonneg_left ha1 (by positivity : 0 ≤ 3 + D)
    linarith only [HI₁, H]
  have HB : (1 + 2 * a * L₀) * I₀ + 20 * a * I₁ ≤ (105 + 40 * C * q + 20 * D) * a := by
    have H0 := mul_le_mul_of_nonneg_left HI₀ (by positivity [ha.1] : 0 ≤ 1 + 2 * a * L₀)
    have H1 := mul_le_mul_of_nonneg_left HI₁' (by positivity [ha.1] : 0 ≤ 20 * a)
    have Hlog := mul_le_mul_of_nonneg_left HL (by positivity [ha.1] : 0 ≤ 10 * a)
    nlinarith only [H0, H1, Hlog]
  have HRtime (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun u => shearTailRadius (α u)) (shearTailRadiusRate (α t)) t := (HT t ht).2.2.2.1
  have HV := abs_sub_le_integral_bound hT HRtime
    (show ContinuousOn (fun t => 256 * a * E t) (Icc (0 : ℝ) T) from continuousOn_const.mul HE)
    (fun t ht => (HT t ht).2.2.2.2.2.2.1)
  rw [intervalIntegral.integral_const_mul] at HV
  have HV' : |F ρ| ≤ 1280 * a ^ 2 := by
    have H0 := mul_le_mul_of_nonneg_left HI₀ (by positivity [ha.1] : 0 ≤ 256 * a)
    nlinarith only [HV, H0]
  have HRvar (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun u => deriv (fun r => shearTailRadius (restartShearTailFlow h a q ζ ν u r)) ρ)
        (shearTailRadiusRateDifferential (α t) (v t)) t := (HT t ht).2.2.2.2.2.1
  have Hcont : ContinuousOn (fun t => 32768 * E t * (1 + 2 * a * L₀ + 20 * a * t)) (Icc (0 : ℝ) T) := by
    fun_prop
  have HD := abs_sub_le_integral_bound hT HRvar Hcont (fun t ht => (HT t ht).2.2.2.2.2.2.2)
  have he (t : ℝ) : 32768 * E t * (1 + 2 * a * L₀ + 20 * a * t) =
      32768 * ((1 + 2 * a * L₀) * E t + (20 * a) * (t * E t)) := by ring
  simp_rw [he] at HD
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (f := fun t => (1 + 2 * a * L₀) * E t) (g := fun t => (20 * a) * (t * E t))
    ((continuousOn_const.mul HE).intervalIntegrable_of_Icc hT)
    ((continuousOn_const.mul (continuousOn_id.mul HE)).intervalIntegrable_of_Icc hT),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at HD
  have HD' : |deriv (fun r => shearTailRadius (restartShearTailFlow h a q ζ ν T r)) ρ -
      deriv (fun r => shearTailRadius (restartShearTailFlow h a q ζ ν 0 r)) ρ| ≤
      32768 * (105 + 40 * C * q + 20 * D) * a := by nlinarith only [HD, HB]
  have HR0 := (HT 0 ⟨le_rfl, hT⟩).2.2.1
  have HRT := (HT T ⟨hT, le_rfl⟩).2.2.1
  have HF : HasDerivAt F (shearTailRadiusDifferential (α T) (v T) -
      shearTailRadiusDifferential (α 0) (v 0)) ρ := HRT.sub HR0
  rw [HRT.deriv, HR0.deriv, ← HF.deriv] at HD'
  refine ⟨HF.differentiableAt, ?_⟩
  nlinarith only [HV', mul_le_mul_of_nonneg_left HD' ha.1.le]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartShearTailPhase_initial (h a q ζ ν : ℝ) :
    restartShearTailPhase h a q ζ ν 0 =
      restartFastShearPhase h (q / 2 * Real.log (1 / a)) 1 ζ ν := by
  funext ρ
  simp only [restartShearTailPhase, shearTailRadius, restartShearTailFlow, zero_add,
    restartFastShearPhase, restartRadialPhase, restartSectionCenterFlow]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearTail_phase_approximation :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 2 < q → 0 ≤ D → ∃ K > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let f := restartShearTailPhase h a q ζ ν (shearTailTime a D)
            let f₀ := fun r => restartReferenceRadialPhase h (restartShearCurve 1 ζ ν r)
            DifferentiableAt ℝ f ρ ∧ |f ρ - f₀ ρ| ≤ K * a ^ 2 ∧
            |deriv f ρ - deriv f₀ ρ| ≤ K * a ∧
            1 / (4 * Real.sqrt 3) ≤ deriv f ρ ∧ deriv f ρ ≤ 2 / Real.sqrt 3 + 1 := by
  obtain ⟨C, hC, hT, hhT, HT⟩ := exists_restartShearTail_radius_transfer
  obtain ⟨hF, hhF, HF⟩ := exists_restartFastShearPhase_monotone
  refine ⟨min hT (min hF (1 / 16)), lt_min hhT (lt_min hhF (by norm_num)), ?_⟩
  intro h hh q D hq hD
  obtain ⟨KF, hKF, HKF⟩ := HF h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  let KT := 1280 + 32768 * (105 + 40 * C * q + 20 * D)
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hKT : 0 < KT := by dsimp only [KT]; positivity
  let K := KT + KF
  have hK : 0 < K := add_pos hKT hKF
  refine ⟨K, hK, ?_⟩
  intro P hP
  obtain ⟨aT, haT, HAT⟩ := HT h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aF, haF, HAF⟩ := HKF q hq
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
  refine ⟨min aT (min aF (1 / (4 * Real.sqrt 3 * K))),
    lt_min haT (lt_min haF (by positivity)), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ f f₀
  let F := fun r => shearTailRadius (restartShearTailFlow h a q ζ ν (shearTailTime a D) r) -
    shearTailRadius (restartShearTailFlow h a q ζ ν 0 r)
  let g := restartFastShearPhase h (q / 2 * Real.log (1 / a)) 1 ζ ν
  have hε' : 0 ≤ ε ∧ ε ≤ 1 / 64 := ⟨hε.1, by linarith only [hε.2]⟩
  obtain ⟨HFD, HFB⟩ := HAT a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  change DifferentiableAt ℝ F ρ at HFD
  change |F ρ| + a * |deriv F ρ| ≤ KT * a ^ 2 at HFB
  obtain ⟨_, HgD, Hgv, Hgd, _, _⟩ :=
    HAF a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
      ε 1 ζ ν hε' (by norm_num) ⟨hζ.1.le, hζ.2.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  have heq : f = fun r => F r / Real.sqrt 3 + g r := by
    funext r
    have H := congrFun (restartShearTailPhase_initial h a q ζ ν) r
    change shearTailRadius (restartShearTailFlow h a q ζ ν 0 r) / Real.sqrt 3 = g r at H
    change shearTailRadius (restartShearTailFlow h a q ζ ν (shearTailTime a D) r) / Real.sqrt 3 = _
    rw [← H]
    dsimp only [F]
    ring
  have HD : HasDerivAt f (deriv F ρ / Real.sqrt 3 + deriv g ρ) ρ := by
    rw [heq]
    exact (HFD.hasDerivAt.div_const _).add HgD.hasDerivAt
  have HFv : |F ρ / Real.sqrt 3| ≤ KT * a ^ 2 := by
    rw [abs_div, abs_of_pos hsqrt]
    exact (div_le_self (abs_nonneg _) hsqrt1).trans
      (by linarith only [HFB, mul_nonneg ha.1.le (abs_nonneg (deriv F ρ))])
  have HFd : |deriv F ρ / Real.sqrt 3| ≤ KT * a := by
    rw [abs_div, abs_of_pos hsqrt]
    apply (div_le_self (abs_nonneg _) hsqrt1).trans
    apply (mul_le_mul_iff_right₀ ha.1).mp
    nlinarith only [HFB, abs_nonneg (F ρ)]
  have Hv : |f ρ - f₀ ρ| ≤ K * a ^ 2 := by
    rw [heq, add_sub_assoc]
    exact (abs_add_le _ _).trans ((add_le_add HFv Hgv).trans_eq (by dsimp only [K]; ring))
  have Hd : |deriv f ρ - deriv f₀ ρ| ≤ K * a := by
    rw [HD.deriv, add_sub_assoc]
    exact (abs_add_le _ _).trans ((add_le_add HFd Hgd).trans_eq (by dsimp only [K]; ring))
  have Href := restartReferenceRadialPhase_shear_derivative
    ⟨hh.1.le, hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
    ha.1 hρ (by norm_num : |(1 : ℝ)| = 1) hε' ⟨hζ.1.le, hζ.2.2⟩ ⟨hν.1.le, hν.2⟩
  have hKa : K * a ≤ 1 / (4 * Real.sqrt 3) := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3 * K)).mp
      (ha.2.trans ((min_le_right _ _).trans (min_le_right _ _)))
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3)).mpr
    nlinarith only [H]
  have hquarter : 1 / (4 * Real.sqrt 3) ≤ 1 :=
    (div_le_one (by positivity : 0 < 4 * Real.sqrt 3)).mpr (by linarith only [hsqrt1])
  refine ⟨HD.differentiableAt, Hv, Hd, ?_, ?_⟩
  · have he : 1 / (2 * Real.sqrt 3) = 2 * (1 / (4 * Real.sqrt 3)) := by ring
    rw [he] at Href
    linarith only [(abs_le.mp Hd).1, Href.2.1, hKa]
  · linarith only [(abs_le.mp Hd).2, Href.2.2, hKa, hquarter]

end
end

/-- The actual growing-circle phase at the tail endpoint has the original reference phase and positive slope. -/
theorem solution :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 2 < q → 2 < D → ∃ K > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let T := shearTailTime a D
            let f := restartShearTailProjectionPhase h a q ζ ν T
            let f₀ := fun r => restartReferenceRadialPhase h (restartShearCurve 1 ζ ν r)
            T + q / 2 * Real.log (1 / a) ∈
              normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0 ∧
            0 < 1 + restartShearTailFlow h a q ζ ν T ρ 0 ∧
            DifferentiableAt ℝ f ρ ∧ |f ρ - f₀ ρ| ≤ K * a ^ 2 ∧
            |deriv f ρ - deriv f₀ ρ| ≤ K * a ∧
            1 / (4 * Real.sqrt 3) ≤ deriv f ρ ∧ deriv f ρ ≤ 2 / Real.sqrt 3 + 1 := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearTail_projection_error
  obtain ⟨hR, hhR, HR⟩ := exists_restartShearTail_phase_approximation
  refine ⟨min hE (min hR (1 / 16)), lt_min hhE (lt_min hhR (by norm_num)), ?_⟩
  intro h hh q D hq hD
  obtain ⟨KE, hKE, HKE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D hq hD
  obtain ⟨KR, hKR, HKR⟩ := HR h
    ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ q D hq (by linarith only [hD])
  let K := KE + KR
  have hK : 0 < K := add_pos hKE hKR
  refine ⟨K, hK, ?_⟩
  intro P hP
  obtain ⟨aE, haE, HAE⟩ := HKE P hP
  obtain ⟨aR, haR, HAR⟩ := HKR P hP
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
  refine ⟨min aE (min aR (1 / (4 * Real.sqrt 3 * K))),
    lt_min haE (lt_min haR (by positivity)), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ T f f₀
  let g := restartShearTailPhase h a q ζ ν T
  let E := fun r => f r - g r
  obtain ⟨Hdom, Hheight, HED, HEv, HEd⟩ :=
    HAE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨HRD, HRv, HRd, _, _⟩ :=
    HAR a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ ε ζ ν hε hζ hν ρ hρ
  have Hsum : HasDerivAt f (deriv E ρ + deriv g ρ) ρ := by
    convert! HED.hasDerivAt.add HRD.hasDerivAt using 1
    ext r
    exact (sub_add_cancel (f r) (g r)).symm
  have Hv : |f ρ - f₀ ρ| ≤ K * a ^ 2 := by
    have he : f ρ - f₀ ρ = E ρ + (g ρ - f₀ ρ) := by dsimp only [E]; ring
    rw [he]
    exact (abs_add_le _ _).trans ((add_le_add HEv HRv).trans_eq (by dsimp only [K]; ring))
  have Hd : |deriv f ρ - deriv f₀ ρ| ≤ K * a := by
    rw [Hsum.deriv, add_sub_assoc]
    exact (abs_add_le _ _).trans ((add_le_add HEd HRd).trans_eq (by dsimp only [K]; ring))
  have Href := restartReferenceRadialPhase_shear_derivative
    ⟨hh.1.le, hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
    ha.1 hρ (by norm_num : |(1 : ℝ)| = 1) ⟨hε.1, by linarith only [hε.2]⟩
    ⟨hζ.1.le, hζ.2.2⟩ ⟨hν.1.le, hν.2⟩
  have hKa : K * a ≤ 1 / (4 * Real.sqrt 3) := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3 * K)).mp
      (ha.2.trans ((min_le_right _ _).trans (min_le_right _ _)))
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3)).mpr
    nlinarith only [H]
  have hquarter : 1 / (4 * Real.sqrt 3) ≤ 1 :=
    (div_le_one (by positivity : 0 < 4 * Real.sqrt 3)).mpr (by linarith only [hsqrt1])
  refine ⟨Hdom, Hheight, Hsum.differentiableAt, Hv, Hd, ?_, ?_⟩
  · have he : 1 / (2 * Real.sqrt 3) = 2 * (1 / (4 * Real.sqrt 3)) := by ring
    rw [he] at Href
    linarith only [(abs_le.mp Hd).1, Href.2.1, hKa]
  · linarith only [(abs_le.mp Hd).2, Href.2.2, hKa, hquarter]
