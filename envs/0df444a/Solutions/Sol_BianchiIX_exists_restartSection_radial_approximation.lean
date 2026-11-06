-- Prove2me | solution 1 for BianchiIX.exists_restartSection_radial_approximation
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:46:25.3549+00:00
-- url     : https://prove2.me/submissions/5b4a50fb-bb34-483f-84d5-3f069012e4e6

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_exists_restartSectionRadiusTail_derivative_bound
import Theorems.Thm_BianchiIX_exists_restartSectionRadius_differential_bounds
import Theorems.Thm_BianchiIX_exists_restartSection_radial_value_approximation
import Theorems.Thm_BianchiIX_hasDerivAt_normalized_components
import Theorems.Thm_BianchiIX_le_exp_of_clock_deriv_le
import Theorems.Thm_BianchiIX_norm_le_exp_of_norm_deriv_clock
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxCurve_wall_sign
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
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
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_restart_cutoff_budget (C C₀ q : ℝ) :
    ∀ᶠ ρ : ℝ in 𝓝[>] 0, (0 < ρ ∧ ρ ≤ 1) ∧ 2 * C₀ * ρ ≤ 1 / 16 ∧
      C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ)) ≤ 1 / 8 := by
  have HI : Tendsto (fun ρ : ℝ => ρ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have HL : Tendsto (fun ρ : ℝ => ρ * Real.log ρ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one, mul_comm] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have HB : Tendsto (fun ρ : ℝ => 2 * C₀ * ρ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using HI.const_mul (2 * C₀)
  have HT : Tendsto (fun ρ : ℝ => C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ))) (𝓝[>] 0) (𝓝 0) := by
    convert! HL.const_mul (-C * C₀ * q) using 1
    · ext ρ
      rw [one_div, Real.log_inv]
      ring
    · simp
  filter_upwards [show ∀ᶠ ρ : ℝ in 𝓝[>] 0, 0 < ρ from self_mem_nhdsWithin,
    HI.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    HB.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    HT.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))] with ρ hρ hρ1 hb ht
  exact ⟨⟨hρ, hρ1.le⟩, hb.le, ht.le⟩

end
end

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

private theorem BianchiIX.restartReferenceRoot_pos {n : ℝ} (hn : n ^ 2 < 1) : 0 < restartReferenceRoot n :=
  Real.sqrt_pos.mpr (sub_pos.mpr hn)

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

private theorem BianchiIX.hasDerivAt_restartReferenceRoot {n : ℝ} (hn : n ^ 2 < 1) :
    HasDerivAt restartReferenceRoot (-n / restartReferenceRoot n) n := by
  convert! (((hasDerivAt_id' n).pow 2).const_sub 1).sqrt (sub_pos.mpr hn).ne' using 1
  simp only [Pi.pow_apply]
  dsimp only [restartReferenceRoot]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartShearFactor {n : ℝ} (hn : n ^ 2 < 1) :
    HasDerivAt restartShearFactor
      (3 * n / (restartReferenceRoot n * (2 + restartReferenceRoot n) ^ 2)) n := by
  have hz := restartReferenceRoot_pos hn
  have hd : 2 + restartReferenceRoot n ≠ 0 := by positivity
  convert! (hasDerivAt_const n (3 : ℝ)).div
    ((hasDerivAt_restartReferenceRoot hn).const_add 2) hd using 1
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartWallFactor {n : ℝ} (hn : n ^ 2 < 1) :
    HasDerivAt restartWallFactor (9 * n / (2 * (2 + restartReferenceRoot n) ^ 3)) n := by
  have hz := restartReferenceRoot_pos hn
  have hd : 2 + restartReferenceRoot n ≠ 0 := by positivity
  have hroot := hasDerivAt_restartReferenceRoot hn
  convert! ((hroot.const_add 1).const_mul 9).div
    (((hroot.const_add 2).pow 2).const_mul 2)
    (by change 2 * (2 + restartReferenceRoot n) ^ 2 ≠ 0; positivity) using 1
  simp only [Pi.pow_apply]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartShearCoupling {n : ℝ} (hn : n ^ 2 < 1) :
    HasDerivAt restartShearCoupling
      (3 * Real.sqrt 3 * (restartReferenceRoot n * (2 + restartReferenceRoot n) + 2 * n ^ 2) /
        (restartReferenceRoot n * (2 + restartReferenceRoot n) ^ 3)) n := by
  have hz := restartReferenceRoot_pos hn
  have hd : 2 + restartReferenceRoot n ≠ 0 := by positivity
  convert! ((hasDerivAt_id' n).const_mul (3 * Real.sqrt 3)).div
    (((hasDerivAt_restartReferenceRoot hn).const_add 2).pow 2) (pow_ne_zero 2 hd) using 1
  simp only [Pi.pow_apply]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restart_transport_cancellation {n : ℝ} (hn : n ^ 2 < 1) :
    n * restartReferenceStrongRate n * deriv restartShearFactor n + restartShearFactor n * n ^ 2 = 0 ∧
    n * restartReferenceStrongRate n * deriv restartWallFactor n +
      restartWallFactor n * restartReferenceWallRate n = 0 ∧
    n * restartReferenceStrongRate n * deriv restartShearCoupling n +
      restartShearFactor n * Real.sqrt 3 * n +
      restartShearCoupling n * restartReferenceWallRate n = 0 := by
  have hz := restartReferenceRoot_pos hn
  have hd : 2 + restartReferenceRoot n ≠ 0 := by positivity
  have hn2 : n ^ 2 = 1 - restartReferenceRoot n ^ 2 := by
    linarith only [restartReferenceRoot_sq hn.le]
  have hF : restartReferenceStrongRate n = -restartReferenceRoot n * (2 + restartReferenceRoot n) := by
    dsimp only [restartReferenceStrongRate]
    rw [hn2]
    ring
  have hb : restartReferenceWallRate n = restartReferenceRoot n * (1 - restartReferenceRoot n) := by
    dsimp only [restartReferenceWallRate]
    rw [hn2]
    ring
  rw [(hasDerivAt_restartShearFactor hn).deriv, (hasDerivAt_restartWallFactor hn).deriv,
    (hasDerivAt_restartShearCoupling hn).deriv, hF, hb]
  dsimp only [restartShearFactor, restartWallFactor, restartShearCoupling]
  constructor
  · field_simp
    ring
  constructor
  · field_simp
    linear_combination -9 * restartReferenceRoot n * (restartReferenceRoot_sq hn.le)
  · field_simp
    linear_combination -6 * Real.sqrt 3 * n * (restartReferenceRoot_sq hn.le)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restart_coefficients {n : ℝ} (hn : n ^ 2 < 1) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartShearFactor n ∧ ContDiffAt ℝ k restartWallFactor n ∧
      ContDiffAt ℝ k restartShearCoupling n := by
  have hr : ContDiffAt ℝ k restartReferenceRoot n :=
    (contDiffAt_const.sub (contDiffAt_id.pow 2)).sqrt (sub_pos.mpr hn).ne'
  have hd : 2 + restartReferenceRoot n ≠ 0 := by positivity [restartReferenceRoot_pos hn]
  refine ⟨contDiffAt_const.div (contDiffAt_const.add hr) hd, ?_, ?_⟩
  · exact (contDiffAt_const.mul (contDiffAt_const.add hr)).div
      (contDiffAt_const.mul ((contDiffAt_const.add hr).pow 2)) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hd))
  · exact (contDiffAt_const.mul contDiffAt_id).div ((contDiffAt_const.add hr).pow 2) (pow_ne_zero 2 hd)

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

private theorem BianchiIX.curvature_restart_decomposition (x : NormalizedState) :
    curvature (x 2) (x 3) (x 4) = x 2 ^ 2 + restartCurvatureDifference x := by
  dsimp only [curvature, restartCurvatureDifference]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restart_negative_branch_root {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) :
    -x 0 = Real.sqrt (1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4)) := by
  have hr : 1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4) = x 0 ^ 2 := by
    dsimp only [stateConstraint, constraint, shearSq] at hc
    linarith only [hc]
  rw [hr, Real.sqrt_sq_eq_abs, abs_of_neg hp]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restart_components {x : ℝ → NormalizedState} {t : ℝ}
    (hx : HasDerivAt x (normalizedField (x t)) t) (hc : stateConstraint (x t) = 1) :
    HasDerivAt (fun r => x r 2)
      (x t 2 * (restartReferenceStrongRate (x t 2) + restartStrongRateDifference (x t))) t ∧
    HasDerivAt (fun r => x r 1)
      (x t 2 ^ 2 * x t 1 + Real.sqrt 3 * x t 2 * (x t 3 - x t 4) +
        (restartCurvatureDifference (x t) * x t 1 - Real.sqrt 3 * (x t 3 + x t 4) * (x t 3 - x t 4))) t ∧
    HasDerivAt (fun r => x r 3 - x r 4)
      (restartReferenceWallRate (x t 2) * (x t 3 - x t 4) +
        (restartCurvatureDifference (x t) + restartRootDifference (x t)) * (x t 3 - x t 4) +
        Real.sqrt 3 * (x t 3 + x t 4) * x t 1) t := by
  obtain ⟨_, hs, hn, ha, hb⟩ := hasDerivAt_normalized_components hx
  have hq : shearSq (x t 0) (x t 1) = 1 - curvature (x t 2) (x t 3) (x t 4) := by
    dsimp only [stateConstraint, constraint] at hc
    linarith only [hc]
  refine ⟨hn.congr_deriv ?_, hs.congr_deriv ?_, (ha.sub hb).congr_deriv ?_⟩
  · dsimp only [rateOne, restartReferenceStrongRate, restartStrongRateDifference, restartRootDifference]
    rw [hq, curvature_restart_decomposition]
    ring
  · dsimp only [shearMinus, curvature, restartCurvatureDifference]
    ring
  · dsimp only [rateTwo, rateThree, restartReferenceWallRate, restartRootDifference]
    rw [hq, curvature_restart_decomposition]
    ring

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

private theorem BianchiIX.contDiff_restartRadicand (k : WithTop ℕ∞) : ContDiff ℝ k restartRadicand := by
  unfold restartRadicand curvature
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartCompactRoot {x : RestartState} (hx : 0 < restartRadicand x)
    (k : WithTop ℕ∞) : ContDiffAt ℝ k restartCompactRoot x :=
  (contDiff_restartRadicand k).contDiffAt.sqrt hx.ne'

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartCompactField {x : RestartState} (hx : 0 < restartRadicand x)
    (k : WithTop ℕ∞) : ContDiffAt ℝ k restartCompactField x := by
  have hr := contDiffAt_restartCompactRoot hx k
  rw [contDiffAt_pi]
  intro i
  fin_cases i <;> dsimp [restartCompactField, restartCompactWeakRate, shearMinus, curvature] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasFDerivAt_restartCompactField_zero : HasFDerivAt (𝕜 := ℝ) restartCompactField 0 0 := by
  have hp (i : Fin 4) := hasFDerivAt_apply (𝕜 := ℝ) i (0 : RestartState)
  have hQ : HasFDerivAt (𝕜 := ℝ) (fun x : RestartState => curvature (x 0) (x 2) (x 3)) 0 0 := by
    have H := (((hp 0).pow 2).add ((hp 2).pow 2) |>.add ((hp 3).pow 2)).sub
      ((((hp 0).mul (hp 2)).add ((hp 2).mul (hp 3)) |>.add ((hp 3).mul (hp 0))).const_mul 2)
    convert! H using 1
    simp
  have hR : HasFDerivAt (𝕜 := ℝ) restartRadicand 0 0 := by
    convert! (((hp 1).pow 2).const_sub 1).sub hQ using 1
    simp
  have hr : HasFDerivAt (𝕜 := ℝ) restartCompactRoot 0 0 := by
    convert! hR.sqrt (by norm_num [restartRadicand, curvature] : restartRadicand 0 ≠ 0) using 1
    simp
  have hH : HasFDerivAt (𝕜 := ℝ) (fun x : RestartState => -(x 2) ^ 2 + (x 3) ^ 2 + x 0 * x 2 - x 0 * x 3) 0 0 := by
    convert! ((((hp 2).pow 2).neg.add ((hp 3).pow 2)).add ((hp 0).mul (hp 2))).sub
      ((hp 0).mul (hp 3)) using 1
    simp
  have hg (ε : ℝ) := ((hQ.sub_const 1).add hr).add ((hp 1).const_mul (ε * Real.sqrt 3))
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · convert! (hQ.sub_const 1).sub (hr.const_mul 2) using 1
    simp
  · convert! (hQ.mul (hp 1)).add (hH.const_mul (Real.sqrt 3)) using 1
    simp [curvature]
  · convert! (hp 2).mul (hg 1) using 1
    simp [curvature, restartCompactRoot, restartRadicand]
  · convert! (hp 3).mul (hg (-1)) using 1
    simp [curvature, restartCompactRoot, restartRadicand]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartCompactField_fderiv_zero : fderiv ℝ restartCompactField 0 = 0 :=
  hasFDerivAt_restartCompactField_zero.fderiv

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restart_transported_components
    {n s v : ℝ → ℝ} {t dF es ev : ℝ} (hn₀ : n t ^ 2 < 1)
    (hn : HasDerivAt n (n t * (restartReferenceStrongRate (n t) + dF)) t)
    (hs : HasDerivAt s (n t ^ 2 * s t + Real.sqrt 3 * n t * v t + es) t)
    (hv : HasDerivAt v (restartReferenceWallRate (n t) * v t + ev) t) :
    HasDerivAt (fun r => restartShearFactor (n r) * s r + restartShearCoupling (n r) * v r)
      (n t * dF * (deriv restartShearFactor (n t) * s t + deriv restartShearCoupling (n t) * v t) +
        restartShearFactor (n t) * es + restartShearCoupling (n t) * ev) t ∧
    HasDerivAt (fun r => restartWallFactor (n r) * v r)
      (n t * dF * deriv restartWallFactor (n t) * v t + restartWallFactor (n t) * ev) t := by
  have HA := (hasDerivAt_restartShearFactor hn₀).differentiableAt.hasDerivAt.comp t hn
  have HC := (hasDerivAt_restartWallFactor hn₀).differentiableAt.hasDerivAt.comp t hn
  have HK := (hasDerivAt_restartShearCoupling hn₀).differentiableAt.hasDerivAt.comp t hn
  obtain ⟨ha, hc, hk⟩ := restart_transport_cancellation hn₀
  constructor
  · convert! (HA.mul hs).add (HK.mul hv) using 1
    simp only [Function.comp_def]
    linear_combination -(s t) * ha - (v t) * hk
  · convert! HC.mul hv using 1
    simp only [Function.comp_def]
    linear_combination -(v t) * hc

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartQuadratic_perturbed
    {n s v : ℝ → ℝ} {t dF es ev : ℝ} (hn₀ : n t ^ 2 < 1)
    (hn : HasDerivAt n (n t * (restartReferenceStrongRate (n t) + dF)) t)
    (hs : HasDerivAt s (n t ^ 2 * s t + Real.sqrt 3 * n t * v t + es) t)
    (hv : HasDerivAt v (restartReferenceWallRate (n t) * v t + ev) t) :
    HasDerivAt (fun r => restartQuadratic (n r) (s r) (v r))
      (n t * dF * restartQuadraticStrongDerivative (n t) (s t) (v t) +
        2 * (restartShearFactor (n t) * s t + restartShearCoupling (n t) * v t) *
          (restartShearFactor (n t) * es + restartShearCoupling (n t) * ev) +
        2 * restartWallFactor (n t) ^ 2 * v t * ev) t := by
  obtain ⟨HS, HV⟩ := hasDerivAt_restart_transported_components hn₀ hn hs hv
  convert! (HS.pow 2).add (HV.pow 2) using 1
  dsimp only [restartQuadraticStrongDerivative]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartQuadratic_normalized {x : ℝ → NormalizedState} {t : ℝ}
    (hx : HasDerivAt x (normalizedField (x t)) t) (hc : stateConstraint (x t) = 1)
    (hn : x t 2 ^ 2 < 1) :
    HasDerivAt (fun r => restartQuadratic (x r 2) (x r 1) (x r 3 - x r 4))
      (x t 2 * restartStrongRateDifference (x t) *
          restartQuadraticStrongDerivative (x t 2) (x t 1) (x t 3 - x t 4) +
        2 * restartCurvatureDifference (x t) * restartQuadratic (x t 2) (x t 1) (x t 3 - x t 4) +
        2 * restartRootDifference (x t) * (x t 3 - x t 4) *
          (restartShearFactor (x t 2) * restartShearCoupling (x t 2) * x t 1 +
            (restartShearCoupling (x t 2) ^ 2 + restartWallFactor (x t 2) ^ 2) * (x t 3 - x t 4)) +
        2 * Real.sqrt 3 * (x t 3 + x t 4) * restartRotationDefect (x t 2) (x t 1) (x t 3 - x t 4)) t := by
  obtain ⟨HN, HS, HV⟩ := hasDerivAt_restart_components hx hc
  have HV' : HasDerivAt (fun r => x r 3 - x r 4)
      (restartReferenceWallRate (x t 2) * (x t 3 - x t 4) +
        ((restartCurvatureDifference (x t) + restartRootDifference (x t)) * (x t 3 - x t 4) +
          Real.sqrt 3 * (x t 3 + x t 4) * x t 1)) t := by
    convert! HV using 1
    ring
  convert! hasDerivAt_restartQuadratic_perturbed hn HN HS HV' using 1
  dsimp only [restartQuadratic, restartRotationDefect]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCompact_box_bounds {x : RestartState} (hx : ‖x‖ ≤ 1 / 16) :
    |curvature (x 0) (x 2) (x 3)| ≤ 9 / 256 ∧
      246 / 256 ≤ restartRadicand x ∧ restartRadicand x ≤ 265 / 256 ∧
      15 / 16 ≤ restartCompactRoot x ∧ restartCompactRoot x ≤ 17 / 16 ∧
      -4 < restartCompactField x 0 ∧ restartCompactField x 0 < -2 := by
  have hc (i : Fin 4) : |x i| ≤ 1 / 16 := (norm_le_pi_norm x i).trans hx
  have hs (i : Fin 4) : (x i) ^ 2 ≤ 1 / 256 := by
    obtain ⟨hl, hu⟩ := abs_le.mp (hc i)
    nlinarith only [hl, hu]
  have hm (i j : Fin 4) : |x i * x j| ≤ 1 / 256 := by
    rw [abs_mul]
    calc
      _ ≤ (1 / 16 : ℝ) * (1 / 16) := mul_le_mul (hc i) (hc j) (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hQ : |curvature (x 0) (x 2) (x 3)| ≤ 9 / 256 := by
    obtain ⟨h02l, h02u⟩ := abs_le.mp (hm 0 2)
    obtain ⟨h23l, h23u⟩ := abs_le.mp (hm 2 3)
    obtain ⟨h30l, h30u⟩ := abs_le.mp (hm 3 0)
    apply abs_le.mpr
    dsimp only [curvature]
    constructor
    · nlinarith only [sq_nonneg (x 0), sq_nonneg (x 2), sq_nonneg (x 3), h02u, h23u, h30u]
    · nlinarith only [hs 0, hs 2, hs 3, h02l, h23l, h30l]
  have hRl : 246 / 256 ≤ restartRadicand x := by
    dsimp only [restartRadicand]
    linarith only [hs 1, (abs_le.mp hQ).2]
  have hRu : restartRadicand x ≤ 265 / 256 := by
    dsimp only [restartRadicand]
    linarith only [sq_nonneg (x 1), (abs_le.mp hQ).1]
  have hr0 : 0 ≤ restartCompactRoot x := Real.sqrt_nonneg _
  have hr2 : restartCompactRoot x ^ 2 = restartRadicand x := Real.sq_sqrt (by linarith only [hRl])
  have hrl : 15 / 16 ≤ restartCompactRoot x := by nlinarith only [hr0, hr2, hRl]
  have hru : restartCompactRoot x ≤ 17 / 16 := by nlinarith only [hr0, hr2, hRu]
  refine ⟨hQ, hRl, hRu, hrl, hru, ?_, ?_⟩
  · change -4 < curvature (x 0) (x 2) (x 3) - 1 - 2 * restartCompactRoot x
    linarith only [(abs_le.mp hQ).1, hru]
  · change curvature (x 0) (x 2) (x 3) - 1 - 2 * restartCompactRoot x < -2
    linarith only [(abs_le.mp hQ).2, hrl]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartCompact_derivative_bounds :
    ∃ C ≥ (1 : ℝ), ∀ x : RestartState, ‖x‖ ≤ 1 / 16 →
      ‖fderiv ℝ restartCompactField x‖ ≤ C * ‖x‖ ∧
        ‖fderiv ℝ (fderiv ℝ restartCompactField) x‖ ≤ C := by
  let S := Metric.closedBall (0 : RestartState) (1 / 16)
  have hreg (x : RestartState) (hx : x ∈ S) : ContDiffAt ℝ 3 restartCompactField x := by
    have H := (restartCompact_box_bounds (by simpa [S] using hx)).2.1
    exact contDiffAt_restartCompactField (by linarith only [H]) 3
  have hq : ContinuousOn (fun x => ‖fderiv ℝ (fderiv ℝ restartCompactField) x‖) S := by
    intro x hx
    exact (((hreg x hx).fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).continuousAt.norm.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : RestartState) (1 / 16)).exists_bound_of_continuousOn hq
  let C := max B 1
  have hbound (x : RestartState) (hx : x ∈ S) :
      ‖fderiv ℝ (fderiv ℝ restartCompactField) x‖ ≤ C := by
    exact (le_abs_self _).trans ((hB x hx).trans (le_max_left B 1))
  have hdiff (x : RestartState) (hx : x ∈ S) : DifferentiableAt ℝ (fderiv ℝ restartCompactField) x :=
    ((hreg x hx).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  refine ⟨C, le_max_right _ _, ?_⟩
  intro x hx
  have hxS : x ∈ S := by simpa [S] using hx
  have hzS : (0 : RestartState) ∈ S := by simp [S]
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound
    (convex_closedBall (0 : RestartState) (1 / 16)) hzS hxS
  exact ⟨by simpa only [restartCompactField_fderiv_zero, sub_zero] using H, hbound x hxS⟩

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

private theorem BianchiIX.restartCenterProjection_section (h : ℝ) (Z : RestartCenterState) :
    restartCenterProjection (restartSectionChart h Z) = Z := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCompactCenterProjection_norm_le (x : RestartState) :
    ‖restartCompactCenterProjection x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  fin_cases i
  · exact norm_le_pi_norm x 1
  · exact norm_le_pi_norm x 2
  · exact norm_le_pi_norm x 3

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartPhysicalCoordinates_norm_le {x : NormalizedState} {R : ℝ} (hR : 0 ≤ R)
    (hn : |x 2| ≤ R) (hZ : ‖restartCenterProjection x‖ ≤ R) :
    ‖restartPhysicalCoordinates x‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  fin_cases i
  · exact hn
  · exact (norm_le_pi_norm (restartCenterProjection x) 0).trans hZ
  · exact (norm_le_pi_norm (restartCenterProjection x) 1).trans hZ
  · exact (norm_le_pi_norm (restartCenterProjection x) 2).trans hZ

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCompactField_physical {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) :
    restartCompactField (restartPhysicalCoordinates x) 0 = rateOne (x 0) (x 1) ∧
      restartCompactCenterProjection (restartCompactField (restartPhysicalCoordinates x)) =
        restartCenterProjection (normalizedField x) := by
  have hroot := restart_negative_branch_root hc hp
  have hq : curvature (x 2) (x 3) (x 4) = 1 - shearSq (x 0) (x 1) := by
    dsimp only [stateConstraint, constraint] at hc
    linarith only [hc]
  constructor
  · change curvature (x 2) (x 3) (x 4) - 1 - 2 * Real.sqrt
      (1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4)) = _
    rw [← hroot, hq]
    dsimp only [rateOne]
    ring
  · ext i
    fin_cases i
    · rfl
    · change x 3 * (curvature (x 2) (x 3) (x 4) - 1 + Real.sqrt
        (1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4)) + 1 * Real.sqrt 3 * x 1) =
        rateTwo (x 0) (x 1) * x 3
      rw [← hroot, hq]
      dsimp only [rateTwo]
      ring
    · change x 4 * (curvature (x 2) (x 3) (x 4) - 1 + Real.sqrt
        (1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4)) + (-1) * Real.sqrt 3 * x 1) =
        rateThree (x 0) (x 1) * x 4
      rw [← hroot, hq]
      dsimp only [rateThree]
      ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartPhysical_shear_bound {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0)
    (hx : ‖restartPhysicalCoordinates x‖ ≤ 1 / 16) : x 0 ≤ -(15 / 16) := by
  have H := (restartCompact_box_bounds hx).2.2.2.1
  have heq : restartCompactRoot (restartPhysicalCoordinates x) = -x 0 :=
    (restart_negative_branch_root hc hp).symm
  rw [heq] at H
  linarith only [H]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCenterField_bound {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ w : RestartState, ‖w‖ ≤ 1 / 16 → ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖)
    {x : NormalizedState} (hc : stateConstraint x = 1) (hp : x 0 < 0)
    (hn : 0 ≤ x 2 ∧ x 2 ≤ 1 / 16) (hZ : ‖restartCenterProjection x‖ ≤ 1 / 16) :
    ‖restartCenterProjection (normalizedField x)‖ ≤
      C * (x 2 + ‖restartCenterProjection x‖) * ‖restartCenterProjection x‖ := by
  let r := ‖restartCenterProjection x‖
  let R := max (x 2) r
  let w : RestartState := ![x 2, 0, 0, 0]
  let S := Metric.closedBall (0 : RestartState) R
  have hR : 0 ≤ R := hn.1.trans (le_max_left _ _)
  have hRsmall : R ≤ 1 / 16 := max_le hn.2 hZ
  have hRsum : R ≤ x 2 + r := max_le (le_add_of_nonneg_right (norm_nonneg _))
    (le_add_of_nonneg_left hn.1)
  have hxS : restartPhysicalCoordinates x ∈ S := by
    simpa [S] using restartPhysicalCoordinates_norm_le hR
      (by simpa only [abs_of_nonneg hn.1] using le_max_left (x 2) r) (le_max_right (x 2) r)
  have hwS : w ∈ S := by
    change ‖w - 0‖ ≤ R
    rw [sub_zero]
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro i
    fin_cases i
    · change |x 2| ≤ R
      rw [abs_of_nonneg hn.1]
      exact le_max_left _ _
    all_goals simpa [w] using hR
  have hdiff (z : RestartState) (hz : z ∈ S) : DifferentiableAt ℝ restartCompactField z := by
    have hzR : ‖z‖ ≤ R := by simpa [S] using hz
    have H := (restartCompact_box_bounds (hzR.trans hRsmall)).2.1
    exact (contDiffAt_restartCompactField (by linarith only [H]) 1).differentiableAt (by norm_num)
  have hbound (z : RestartState) (hz : z ∈ S) : ‖fderiv ℝ restartCompactField z‖ ≤ C * R := by
    have hzR : ‖z‖ ≤ R := by simpa [S] using hz
    exact (hF z (hzR.trans hRsmall)).trans (mul_le_mul_of_nonneg_left hzR hC)
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound (convex_closedBall (0 : RestartState) R) hwS hxS
  have hdist : ‖restartPhysicalCoordinates x - w‖ ≤ r := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg (restartCenterProjection x))).mpr
    intro i
    fin_cases i
    · change |x 2 - x 2| ≤ r
      simpa only [sub_self, abs_zero] using norm_nonneg (restartCenterProjection x)
    · change |x 1 - 0| ≤ r
      rw [sub_zero]
      exact norm_le_pi_norm (restartCenterProjection x) 0
    · change |x 3 - 0| ≤ r
      rw [sub_zero]
      exact norm_le_pi_norm (restartCenterProjection x) 1
    · change |x 4 - 0| ≤ r
      rw [sub_zero]
      exact norm_le_pi_norm (restartCenterProjection x) 2
  have hzero : restartCompactCenterProjection (restartCompactField w) = 0 := by
    ext i
    fin_cases i <;> simp [restartCompactCenterProjection, restartCompactField, w, shearMinus]
  rw [← (restartCompactField_physical hc hp).2]
  have heq : restartCompactCenterProjection (restartCompactField (restartPhysicalCoordinates x)) =
      restartCompactCenterProjection (restartCompactField (restartPhysicalCoordinates x) - restartCompactField w) := by
    rw [map_sub, hzero, sub_zero]
  rw [heq]
  exact (restartCompactCenterProjection_norm_le _).trans
    (H.trans ((mul_le_mul_of_nonneg_left hdist (mul_nonneg hC hR)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRsum hC) (norm_nonneg _))))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_restartFastBudget (C h b t : ℝ) :
    HasDerivAt (restartFastBudget C h b) (C * (h * Real.exp (-2 * t) + b)) t := by
  convert! (((((hasDerivAt_id' t).const_mul (-2)).exp.const_sub 1).const_mul (h / 2)).add
    ((hasDerivAt_id' t).const_mul b)).const_mul C using 1
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartFastBudget_zero (C h b : ℝ) : restartFastBudget C h b 0 = 0 := by
  simp [restartFastBudget]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartFastBudget_le {C h b T t : ℝ} (hC : 0 ≤ C) (hh : 0 ≤ h) (hb : 0 ≤ b)
    (ht : t ≤ T) : restartFastBudget C h b t ≤ C * h / 2 + C * b * T := by
  have H := mul_nonneg (mul_nonneg hC hh) (Real.exp_pos (-2 * t)).le
  have Ht := mul_le_mul_of_nonneg_left ht (mul_nonneg hC hb)
  dsimp only [restartFastBudget]
  nlinarith only [H, Ht]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exp_one_quarter_lt_two : Real.exp (1 / 4 : ℝ) < 2 := by
  have H := Real.exp_lt_two_add_div_two_sub (x := (1 : ℝ) / 4) (by norm_num) (by norm_num)
  norm_num at H
  linarith only [H]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restart_fastLayer_prefix {C h b T : ℝ} {α : ℝ → NormalizedState}
    (hC : 0 ≤ C)
    (hF : ∀ w : RestartState, ‖w‖ ≤ 1 / 16 → ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖)
    (hh : 2 * h ≤ 1 / 16) (hb : b ≤ 1 / 16)
    (hα : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt α (normalizedField (α t)) t)
    (hc : ∀ t ∈ Icc (0 : ℝ) T, stateConstraint (α t) = 1)
    (hn : ∀ t ∈ Icc (0 : ℝ) T, 0 < α t 2)
    (hregion : ∀ t ∈ Icc (0 : ℝ) T, restartControlRegion h b (α t))
    (hinit : α 0 2 ≤ h) :
    ∀ t ∈ Icc (0 : ℝ) T,
      α t 2 ≤ h * Real.exp (-2 * t) ∧ α t 0 ≤ -(15 / 16) ∧
        ‖restartCenterProjection (α t)‖ ≤
          ‖restartCenterProjection (α 0)‖ * Real.exp (restartFastBudget C h b t) := by
  have hbox (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖restartPhysicalCoordinates (α t)‖ ≤ 1 / 16 :=
    restartPhysicalCoordinates_norm_le (by norm_num)
      (by rw [abs_of_pos (hn t ht)]; exact (hregion t ht).2.1.trans hh) ((hregion t ht).2.2.trans hb)
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : α t 0 < 0 := by
    have H := (hregion t ht).1
    linarith only [H]
  have hdecay (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : α t 2 ≤ h * Real.exp (-2 * t) := by
    have HD (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) :=
      (hasDerivAt_normalized_components (hα s ⟨hs.1, hs.2.trans ht.2⟩)).2.2.1
    have HB (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) :
        rateOne (α s 0) (α s 1) * α s 2 ≤ -2 * α s 2 := by
      have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
      have H := (restartCompact_box_bounds (hbox s hsT)).2.2.2.2.2.2
      rw [(restartCompactField_physical (hc s hsT) (hp s hsT)).1] at H
      exact mul_le_mul_of_nonneg_right H.le (hn s hsT).le
    have H := le_exp_of_linear_deriv_le (convex_Icc (0 : ℝ) t) HD HB
      (s := 0) (t := t) ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩ ht.1
    have H' : α t 2 ≤ α 0 2 * Real.exp (-2 * t) := by simpa only [sub_zero] using H
    exact H'.trans (mul_le_mul_of_nonneg_right hinit (Real.exp_pos _).le)
  have HD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun s => restartCenterProjection (α s))
        (restartCenterProjection (normalizedField (α t))) t := by
    convert! restartCenterProjection.hasFDerivAt.comp_hasDerivAt t (hα t ht) using 1
  have HB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ‖restartCenterProjection (normalizedField (α t))‖ ≤
        (C * (h * Real.exp (-2 * t) + b)) * ‖restartCenterProjection (α t)‖ := by
    have H := restartCenterField_bound hC hF (hc t ht) (hp t ht)
      ⟨(hn t ht).le, (hregion t ht).2.1.trans hh⟩ ((hregion t ht).2.2.trans hb)
    exact H.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add (hdecay t ht) (hregion t ht).2.2) hC) (norm_nonneg _))
  have HG := norm_le_exp_of_norm_deriv_clock HD (fun t _ => hasDerivAt_restartFastBudget C h b t) HB
  intro t ht
  refine ⟨hdecay t ht, restartPhysical_shear_bound (hc t ht) (hp t ht) (hbox t ht), ?_⟩
  simpa only [restartFastBudget_zero, sub_zero] using HG t ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.isClosed_restartControlRegion (h b : ℝ) : IsClosed {x | restartControlRegion h b x} :=
  (isClosed_le (continuous_apply 0) continuous_const).inter
    ((isClosed_le (continuous_apply 2) continuous_const).inter
      (isClosed_le restartCenterProjection.continuous.norm continuous_const))

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalized_restart_fastLayer_control {C h b T : ℝ} {x : NormalizedState}
    (hC : 0 ≤ C)
    (hF : ∀ w : RestartState, ‖w‖ ≤ 1 / 16 → ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖)
    (hh : 0 < h ∧ h ≤ 1 / 128) (hb : 0 < b ∧ b ≤ 1 / 16) (_hT : 0 ≤ T)
    (hbudget : C * h / 2 + C * b * T ≤ 1 / 4)
    (hc : stateConstraint x = 1) (hp : x 0 < 0) (hn : 0 < x 2 ∧ x 2 ≤ h)
    (hZ : ‖restartCenterProjection x‖ ≤ b / 2) :
    ∀ t ∈ Icc (0 : ℝ) T,
      let y := normalizedMaxCurve x 0 t
      0 < y 2 ∧ y 2 ≤ h * Real.exp (-2 * t) ∧ y 0 ≤ -(15 / 16) ∧
        ‖restartCenterProjection y‖ ≤ ‖restartCenterProjection x‖ * Real.exp (restartFastBudget C h b t) ∧
        ‖restartCenterProjection y‖ < b := by
  let α := normalizedMaxCurve x 0
  let S := {t : ℝ | restartControlRegion h b (α t)}
  have hα (t : ℝ) (ht : 0 ≤ t) : HasDerivAt α (normalizedField (α t)) t :=
    (normalizedMaxCurve_forward_of_constraint hc ht).1
  have hcon (t : ℝ) (ht : 0 ≤ t) : stateConstraint (α t) = 1 :=
    (normalizedMaxCurve_forward_of_constraint hc ht).2.1
  have hpos (t : ℝ) (ht : 0 ≤ t) : 0 < α t 2 := by
    have H := normalizedMaxCurve_wall_sign hc ht (0 : Fin 3)
    change (α t 2 = 0 ↔ x 2 = 0) ∧ (0 ≤ α t 2 ↔ 0 ≤ x 2) at H
    have hne : α t 2 ≠ 0 := fun he => hn.1.ne' (H.1.mp he)
    exact lt_of_le_of_ne (H.2.mpr hn.1.le) hne.symm
  have hinit : α 0 = x := normalizedMaxCurve_initial x 0
  have hhsmall : 2 * h ≤ 1 / 16 := by linarith only [hh.2]
  have hZsmall : ‖restartCenterProjection x‖ ≤ 1 / 16 := by linarith only [hZ, hb.2]
  have hpx : x 0 ≤ -(15 / 16) := restartPhysical_shear_bound hc hp
    (restartPhysicalCoordinates_norm_le (by norm_num)
      (by rw [abs_of_pos hn.1]; linarith only [hn.2, hh.2]) hZsmall)
  have hS0 : (0 : ℝ) ∈ S := by
    change restartControlRegion h b (α 0)
    rw [hinit]
    exact ⟨by linarith only [hpx], by linarith only [hn.2, hh.1], by linarith only [hZ, hb.1]⟩
  have hclosed : IsClosed (S ∩ Icc 0 T) := by
    have H := (HasDerivAt.continuousOn (fun t (ht : t ∈ Icc (0 : ℝ) T) => hα t ht.1)).preimage_isClosed_of_isClosed
      isClosed_Icc (isClosed_restartControlRegion h b)
    convert! H using 1
    ext t
    change (restartControlRegion h b (α t) ∧ t ∈ Icc 0 T) ↔
      (t ∈ Icc 0 T ∧ restartControlRegion h b (α t))
    tauto
  have hstrict {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
      (HZ : ‖restartCenterProjection (α t)‖ ≤
        ‖restartCenterProjection (α 0)‖ * Real.exp (restartFastBudget C h b t)) :
      ‖restartCenterProjection (α t)‖ < b := by
    rw [hinit] at HZ
    have HE := (restartFastBudget_le hC hh.1.le hb.1.le ht.2).trans hbudget
    have hbhalf : 0 < b / 2 := div_pos hb.1 (by norm_num)
    have H := HZ.trans (mul_le_mul hZ (Real.exp_le_exp.mpr HE) (Real.exp_pos _).le hbhalf.le)
    have H' := mul_lt_mul_of_pos_left exp_one_quarter_lt_two hbhalf
    nlinarith only [H, H']
  have hwhole : Icc (0 : ℝ) T ⊆ S := by
    apply hclosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hS0
    intro t ht hbefore
    have H := restart_fastLayer_prefix hC hF hhsmall hb.2
      (fun u hu => hα u hu.1) (fun u hu => hcon u hu.1) (fun u hu => hpos u hu.1)
      (fun u hu => hbefore hu) (by rw [hinit]; exact hn.2) t ⟨ht.1, le_rfl⟩
    have hpstrict : α t 0 < -(1 / 2) := by linarith only [H.2.1]
    have hnstrict : α t 2 < 2 * h := by
      have he := Real.exp_le_one_iff.mpr (by linarith only [ht.1] : -2 * t ≤ 0)
      have Hn := H.1.trans (mul_le_mul_of_nonneg_left he hh.1.le)
      nlinarith only [Hn, hh.1]
    have hZstrict := hstrict ⟨ht.1, ht.2.le⟩ H.2.2
    have hpcont := (continuous_apply (0 : Fin 5)).continuousAt.comp (hα t ht.1).continuousAt
    have hncont := (continuous_apply (2 : Fin 5)).continuousAt.comp (hα t ht.1).continuousAt
    have hZcont := (restartCenterProjection.continuous.continuousAt.comp (hα t ht.1).continuousAt).norm
    have Hev : ∀ᶠ u in 𝓝 t, u ∈ S := by
      filter_upwards [hpcont.eventually (isOpen_Iio.mem_nhds hpstrict),
        hncont.eventually (isOpen_Iio.mem_nhds hnstrict),
        hZcont.eventually (isOpen_Iio.mem_nhds hZstrict)] with u hpu hnu hZu
      exact ⟨hpu.le, hnu.le, hZu.le⟩
    exact Hev.filter_mono nhdsWithin_le_nhds
  have H := restart_fastLayer_prefix hC hF hhsmall hb.2
    (fun u hu => hα u hu.1) (fun u hu => hcon u hu.1) (fun u hu => hpos u hu.1)
    (fun u hu => hwhole hu) (by rw [hinit]; exact hn.2)
  intro t ht
  have Ht := H t ht
  refine ⟨hpos t ht.1, Ht.1, Ht.2.1, ?_, hstrict ht Ht.2.2⟩
  simpa only [hinit] using Ht.2.2

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_normalized_restart_fastLayer_control :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ) (x : NormalizedState),
      (0 < h ∧ h ≤ 1 / 128) → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T →
      C * h / 2 + C * b * T ≤ 1 / 4 → stateConstraint x = 1 → x 0 < 0 →
      (0 < x 2 ∧ x 2 ≤ h) → ‖restartCenterProjection x‖ ≤ b / 2 →
      ∀ t ∈ Icc (0 : ℝ) T,
        let y := normalizedMaxCurve x 0 t
        0 < y 2 ∧ y 2 ≤ h * Real.exp (-2 * t) ∧ y 0 ≤ -(15 / 16) ∧
          ‖restartCenterProjection y‖ ≤ ‖restartCenterProjection x‖ * Real.exp (restartFastBudget C h b t) ∧
          ‖restartCenterProjection y‖ < b := by
  obtain ⟨A, _, HA⟩ := exists_restartCompact_derivative_bounds
  let C := max A 32
  have hC : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 32) (le_max_right A 32)
  have hF (w : RestartState) (hw : ‖w‖ ≤ 1 / 16) : ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖ :=
    (HA w hw).1.trans (mul_le_mul_of_nonneg_right (le_max_left A 32) (norm_nonneg w))
  exact ⟨C, le_max_right _ _, fun _ _ _ _ => normalized_restart_fastLayer_control hC hF⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartSection_fastLayer_control :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ) (Z : RestartCenterState),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T →
      C * b * T ≤ 1 / 8 → ‖Z‖ ≤ b / 2 →
      ∀ t ∈ Icc (0 : ℝ) T,
        let x := normalizedMaxCurve (restartSectionChart h Z) 0 t
        0 < x 2 ∧ x 2 ≤ h * Real.exp (-2 * t) ∧ x 0 ≤ -(15 / 16) ∧
          ‖restartSectionCenterFlow h t Z‖ ≤ ‖Z‖ * Real.exp (restartFastBudget C h b t) ∧
          ‖restartSectionCenterFlow h t Z‖ < b := by
  obtain ⟨C, hC, HC⟩ := exists_normalized_restart_fastLayer_control
  refine ⟨C, hC, ?_⟩
  intro h b T Z hh hCh hb hT hCb hZ
  have hhsmall : h ≤ 1 / 128 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.le]
  let w : RestartState := ![h, Z 0, Z 1, Z 2]
  have hw : ‖w‖ ≤ 1 / 16 := by
    have hZsmall : ‖Z‖ ≤ 1 / 16 := by linarith only [hZ, hb.2]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16)).mpr
    intro i
    fin_cases i
    · change |h| ≤ 1 / 16
      rw [abs_of_pos hh]
      linarith only [hhsmall]
    · exact (norm_le_pi_norm Z 0).trans hZsmall
    · exact (norm_le_pi_norm Z 1).trans hZsmall
    · exact (norm_le_pi_norm Z 2).trans hZsmall
  have hr : 0 < restartSectionRadicand h Z := by
    have H := (restartCompact_box_bounds hw).2.1
    change 246 / 256 ≤ restartSectionRadicand h Z at H
    linarith only [H]
  have hp : restartSectionChart h Z 0 < 0 := neg_lt_zero.mpr (Real.sqrt_pos.mpr hr)
  have hbudget : C * h / 2 + C * b * T ≤ 1 / 4 := by linarith only [hCh, hCb]
  have H := HC h b T (restartSectionChart h Z) ⟨hh, hhsmall⟩ hb hT hbudget
    (restartSectionChart_constraint hr.le) hp ⟨hh, le_rfl⟩
    (by simpa only [restartCenterProjection_section] using hZ)
  intro t ht
  simpa only [restartCenterProjection_section, restartSectionCenterFlow] using H t ht

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionRadicand_pos_of_small {h : ℝ} {Z : RestartCenterState}
    (hh : |h| ≤ 1 / 16) (hZ : ‖Z‖ ≤ 1 / 16) : 0 < restartSectionRadicand h Z := by
  have hw := restartPhysicalCoordinates_norm_le (x := restartSectionChart h Z) (by norm_num : (0 : ℝ) ≤ 1 / 16)
    hh (by rwa [restartCenterProjection_section])
  have H := (restartCompact_box_bounds hw).2.1
  change 246 / 256 ≤ restartSectionRadicand h Z at H
  linarith only [H]

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

private theorem BianchiIX.deriv_restartGramCoefficients {n : ℝ} (hn : n ^ 2 < 1) :
    deriv restartGramCoefficients n =
      ![2 * restartShearFactor n * deriv restartShearFactor n,
        2 * (deriv restartShearFactor n * restartShearCoupling n +
          restartShearFactor n * deriv restartShearCoupling n),
        2 * (restartShearCoupling n * deriv restartShearCoupling n +
          restartWallFactor n * deriv restartWallFactor n)] := by
  have ha := (hasDerivAt_restartShearFactor hn).differentiableAt.hasDerivAt
  have hc := (hasDerivAt_restartWallFactor hn).differentiableAt.hasDerivAt
  have hk := (hasDerivAt_restartShearCoupling hn).differentiableAt.hasDerivAt
  apply HasDerivAt.deriv
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivAt (fun m => restartShearFactor m ^ 2)
      (2 * restartShearFactor n * deriv restartShearFactor n) n
    convert! ha.pow 2 using 1
    ring
  · change HasDerivAt (fun m => 2 * restartShearFactor m * restartShearCoupling m)
      (2 * (deriv restartShearFactor n * restartShearCoupling n +
        restartShearFactor n * deriv restartShearCoupling n)) n
    convert! (ha.const_mul 2).mul hk using 1
    ring
  · change HasDerivAt (fun m => restartShearCoupling m ^ 2 + restartWallFactor m ^ 2)
      (2 * (restartShearCoupling n * deriv restartShearCoupling n +
        restartWallFactor n * deriv restartWallFactor n)) n
    convert! (hk.pow 2).add (hc.pow 2) using 1
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartRadialDrift_formula {p : RestartRadialState} (hn : p.1 ^ 2 < 1) :
    restartRadialDrift p =
      p.1 * (restartRadialCurvatureDifference p - 2 * restartRadialRootDifference p) *
        restartQuadraticStrongDerivative p.1 (p.2 0) (p.2 1 - p.2 2) +
      2 * restartRadialCurvatureDifference p * restartQuadratic p.1 (p.2 0) (p.2 1 - p.2 2) +
      2 * restartRadialRootDifference p * (p.2 1 - p.2 2) *
        (restartShearFactor p.1 * restartShearCoupling p.1 * p.2 0 +
          (restartShearCoupling p.1 ^ 2 + restartWallFactor p.1 ^ 2) * (p.2 1 - p.2 2)) +
      2 * Real.sqrt 3 * (p.2 1 + p.2 2) * restartRotationDefect p.1 (p.2 0) (p.2 1 - p.2 2) := by
  unfold restartRadialDrift restartRadialDriftCoefficients
  rw [deriv_restartGramCoefficients hn]
  dsimp [quadraticFromCoefficients, restartGramCoefficients, restartRootCoefficients,
    restartRotationCoefficients, restartQuadraticStrongDerivative, restartQuadratic, restartRotationDefect]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartQuadratic_drift {x : ℝ → NormalizedState} {t : ℝ}
    (hx : HasDerivAt x (normalizedField (x t)) t) (hc : stateConstraint (x t) = 1)
    (hp : x t 0 < 0) (hn : x t 2 ^ 2 < 1) :
    HasDerivAt (fun r => restartQuadratic (x r 2) (x r 1) (x r 3 - x r 4))
      (restartRadialDrift (x t 2, restartCenterProjection (x t))) t := by
  apply (hasDerivAt_restartQuadratic_normalized hx hc hn).congr_deriv
  rw [restartRadialDrift_formula hn]
  have hroot := restart_negative_branch_root hc hp
  change -x t 0 = Real.sqrt (restartSectionRadicand (x t 2) (restartCenterProjection (x t))) at hroot
  dsimp only [restartRadialRootDifference]
  rw [← hroot]
  rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartRadialQuadratic {p : RestartRadialState}
    (hn : p.1 ^ 2 < 1) (k : WithTop ℕ∞) : ContDiffAt ℝ k restartRadialQuadratic p := by
  obtain ⟨ha, hc, hk⟩ := contDiffAt_restart_coefficients hn k
  have hA := ha.comp p contDiffAt_fst
  have hC := hc.comp p contDiffAt_fst
  have hK := hk.comp p contDiffAt_fst
  unfold restartRadialQuadratic restartQuadratic
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartSectionQuadratic_initial (h : ℝ) (Z : RestartCenterState) :
    restartSectionQuadratic h 0 Z = restartQuadratic h (Z 0) (Z 1 - Z 2) := by
  simp only [restartSectionQuadratic, restartSectionStrongWall, restartSectionCenterFlow,
    normalizedMaxCurve_initial, restartCenterProjection_section]
  rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartSectionRadius {h t : ℝ} {Z : RestartCenterState}
    (HD : HasDerivAt (fun s => restartSectionQuadratic h s Z) (restartSectionQuadraticRate h t Z) t)
    (HJ : 0 < restartSectionQuadratic h t Z) :
    HasDerivAt (fun s => restartSectionRadius h s Z)
      (restartSectionQuadraticRate h t Z / (2 * restartSectionRadius h t Z)) t :=
  HD.sqrt HJ.ne'

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_restartSectionRadialState_joint {h : ℝ} {p : RestartCenterState × ℝ}
    (hr : 0 < restartSectionRadicand h p.1)
    (ht : p.2 ∈ normalizedMaxDomain (restartSectionChart h p.1) 0) :
    ContDiffAt ℝ 2 (fun q : RestartCenterState × ℝ => restartSectionRadialState h q.2 q.1) p := by
  have HX : ContDiffAt ℝ 2
      (fun q : RestartCenterState × ℝ => normalizedMaxCurve (restartSectionChart h q.1) 0 q.2) p :=
    (contDiffAt_normalizedMaxCurve_two ht).comp p
      (g := fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 0 z.2)
      (((contDiffAt_restartSectionChart hr 2).comp p contDiffAt_fst).prodMk contDiffAt_snd)
  exact ((contDiffAt_apply ℝ ℝ (2 : Fin 5) _).comp p HX).prodMk
    (restartCenterProjection.contDiff.contDiffAt.comp p HX)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_restartSectionRadius_joint {h : ℝ} {p : RestartCenterState × ℝ}
    (hp : restartSectionRadiusRegular h p) :
    ContDiffAt ℝ 2 (fun q : RestartCenterState × ℝ => restartSectionRadius h q.2 q.1) p := by
  have Hstate := contDiffAt_restartSectionRadialState_joint hp.1 hp.2.1
  have HQ := (contDiffAt_restartRadialQuadratic (p := restartSectionRadialState h p.2 p.1) hp.2.2.2.1 2).comp p Hstate
  exact HQ.sqrt hp.2.2.2.2.ne'

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionRadiusRegular_eventually {h : ℝ} {p : RestartCenterState × ℝ}
    (hp : restartSectionRadiusRegular h p) : ∀ᶠ q in 𝓝 p, restartSectionRadiusRegular h q := by
  have Hchart := (contDiffAt_restartSectionChart hp.1 2).comp p contDiffAt_fst
  have HX : ContDiffAt ℝ 2
      (fun q : RestartCenterState × ℝ => normalizedMaxCurve (restartSectionChart h q.1) 0 q.2) p :=
    (contDiffAt_normalizedMaxCurve_two hp.2.1).comp p
      (g := fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 0 z.2) (Hchart.prodMk contDiffAt_snd)
  have Hr : ContinuousAt (fun q : RestartCenterState × ℝ => restartSectionRadicand h q.1) p := by
    unfold restartSectionRadicand curvature
    fun_prop
  have Hneg := (continuous_apply (0 : Fin 5)).continuousAt.comp HX.continuousAt
  have Hn := ((continuous_apply (2 : Fin 5)).continuousAt.comp HX.continuousAt).pow 2
  have HQ := (contDiffAt_restartRadialQuadratic (p := restartSectionRadialState h p.2 p.1) hp.2.2.2.1 2).comp p
    (contDiffAt_restartSectionRadialState_joint hp.1 hp.2.1)
  filter_upwards [Hr.eventually (isOpen_Ioi.mem_nhds hp.1),
    (Hchart.continuousAt.prodMk continuousAt_snd).eventually ((isOpen_normalizedFlowDomain 0).mem_nhds hp.2.1),
    Hneg.eventually (isOpen_Iio.mem_nhds hp.2.2.1), Hn.eventually (isOpen_Iio.mem_nhds hp.2.2.2.1),
    HQ.continuousAt.eventually (isOpen_Ioi.mem_nhds hp.2.2.2.2)] with q hqr hqt hqp hqn hqJ
  exact ⟨hqr, hqt, hqp, hqn, hqJ⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartSectionRadius_time {h t : ℝ} {Z : RestartCenterState}
    (hp : restartSectionRadiusRegular h (Z, t)) :
    HasDerivAt (fun s => restartSectionRadius h s Z) (restartSectionRadiusRate h t Z) t := by
  have HJ := hasDerivAt_restartQuadratic_drift (hasDerivAt_normalizedMaxCurve hp.2.1)
    ((normalizedMaxCurve_constraint hp.2.1).trans (restartSectionChart_constraint hp.1.le))
    hp.2.2.1 hp.2.2.2.1
  exact hasDerivAt_restartSectionRadius HJ hp.2.2.2.2

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionRadius_local_time {h : ℝ} {p : RestartCenterState × ℝ}
    (hp : restartSectionRadiusRegular h p) :
    (fun q => fderiv ℝ (fun z : RestartCenterState × ℝ => restartSectionRadius h z.2 z.1) q (0, 1)) =ᶠ[𝓝 p]
      (fun q => restartSectionRadiusRate h q.2 q.1) := by
  filter_upwards [restartSectionRadiusRegular_eventually hp] with q hq
  have H := ((contDiffAt_restartSectionRadius_joint hq).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt q.2
    ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))
  exact H.unique (hasDerivAt_restartSectionRadius_time hq)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartSectionRadius_variation {h t : ℝ} {Z : RestartCenterState}
    (hp : restartSectionRadiusRegular h (Z, t)) (v : RestartCenterState) :
    HasDerivAt (fun s => fderiv ℝ (restartSectionRadius h s) Z v)
      (fderiv ℝ (restartSectionRadiusRate h t) Z v) t :=
  hasDerivAt_parameter_fderiv_of_local_time (contDiffAt_restartSectionRadius_joint hp)
    (restartSectionRadius_local_time hp) v

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartSectionRadius_derivative_error :
    ∃ C ≥ (32 : ℝ), ∀ c : ℝ, 0 < c → ∃ K : ℝ, 0 < K ∧
      ∀ (h b T : ℝ) (Z : RestartCenterState),
        0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
        ‖Z‖ ≤ b / 2 → c * b ≤ restartRadialNorm Z → ∀ t ∈ Icc (0 : ℝ) T,
          DifferentiableAt ℝ (fun W => restartSectionRadius h t W - restartSectionRadius h 0 W) Z ∧
          ‖fderiv ℝ (fun W => restartSectionRadius h t W - restartSectionRadius h 0 W) Z‖ ≤
            K * (h * b + b ^ 2 * t) := by
  obtain ⟨A, hA, HA⟩ := exists_restartSectionRadius_differential_bounds
  obtain ⟨B, _, HB⟩ := exists_restartSection_fastLayer_control
  let C := max A B
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := le_max_right _ _
  have hC : 32 ≤ C := hA.trans hAC
  refine ⟨C, hC, ?_⟩
  intro c hc
  obtain ⟨K, hK, HK⟩ := HA c hc
  refine ⟨K, hK, ?_⟩
  intro h b T Z hh hCh hb hT hCb hZ hradial
  have hbpos : 0 < b := hb.1
  have hb0 : 0 ≤ b := hb.1.le
  have Hheight (k : ℝ) (hk : k ≤ C) : k * h ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_right hk hh.le).trans hCh
  have Htime (k : ℝ) (hk : k ≤ C) : k * b * T ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk hb0) hT).trans hCb
  have H := HK h b T Z hh (Hheight A hAC) hb hT (Htime A hAC) hZ hradial
  have HF := HB h b T Z hh (Hheight B hBC) hb hT (Htime B hBC) hZ
  have hhsmall : h ≤ 1 / 16 := by nlinarith only [hC, hCh, hh]
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rwa [abs_of_pos hh]) (by linarith only [hZ, hb.2])
  have Hreg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : restartSectionRadiusRegular h (Z, t) := by
    have Hn : restartSectionStrongWall h t Z ≤ 1 / 16 :=
      (HF t ht).2.1.trans ((mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (by linarith only [ht.1] : -2 * t ≤ 0)) hh.le).trans (by simpa using hhsmall))
    have HR : 0 < restartSectionRadius h t Z :=
      (by positivity : 0 < c * b / 2).trans_le (H t ht).1
    refine ⟨hrad, normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 ht.1,
      ?_, ?_, Real.sqrt_pos.mp HR⟩
    · change normalizedMaxCurve (restartSectionChart h Z) 0 t 0 < 0
      linarith only [(HF t ht).2.2.1]
    · change restartSectionStrongWall h t Z ^ 2 < 1
      have Hnpos : 0 < restartSectionStrongWall h t Z := (HF t ht).1
      nlinarith only [Hnpos, Hn]
  have Hzero := H 0 ⟨le_rfl, hT⟩
  intro t ht
  have HD := (H t ht).2.1.hasFDerivAt.sub Hzero.2.1.hasFDerivAt
  change HasFDerivAt (fun W => restartSectionRadius h t W - restartSectionRadius h 0 W) _ Z at HD
  refine ⟨HD.differentiableAt, ?_⟩
  rw [HD.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [ht.1])
  intro v
  have Hrate (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      |fderiv ℝ (restartSectionRadiusRate h s) Z v| ≤
        (K * ‖v‖) * ((h * b) * Real.exp (-2 * s) + b ^ 2) := by
    calc
      _ ≤ ‖fderiv ℝ (restartSectionRadiusRate h s) Z‖ * ‖v‖ :=
        (fderiv ℝ (restartSectionRadiusRate h s) Z).le_opNorm v
      _ ≤ (K * (restartSectionStrongWall h s Z * b + b ^ 2)) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (H s hs).2.2.2.2 (norm_nonneg _)
      _ ≤ (K * ((h * Real.exp (-2 * s)) * b + b ^ 2)) * ‖v‖ := by
        gcongr
        exact (HF s hs).2.1
      _ = _ := by ring
  have HP := abs_sub_le_of_deriv_primitive
    (fun s hs => hasDerivAt_restartSectionRadius_variation (Hreg s hs) v)
    (fun s _ => hasDerivAt_restartFastBudget (K * ‖v‖) (h * b) (b ^ 2) s) Hrate
  have HV := HP t ht
  rw [restartFastBudget_zero, sub_zero] at HV
  have HE := restartFastBudget_le (by positivity : 0 ≤ K * ‖v‖)
    (by positivity : 0 ≤ h * b) (sq_nonneg b) (T := t) le_rfl
  change |fderiv ℝ (restartSectionRadius h t) Z v - fderiv ℝ (restartSectionRadius h 0) Z v| ≤ _
  exact HV.trans (by
    nlinarith only [HE, mul_nonneg (mul_nonneg (mul_nonneg hK.le (norm_nonneg v)) hh.le) hb0])

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionRadialError_eq (h t : ℝ) (Z : RestartCenterState) :
    restartSectionRadialError h t Z =
      (restartRadialNorm (restartSectionCenterFlow h t Z) - restartSectionRadius h 0 Z) / Real.sqrt 3 := by
  dsimp only [restartSectionRadialError, restartRadialPhase, restartReferenceRadialPhase, restartSectionRadius]
  rw [restartSectionQuadratic_initial]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionRadialError_derivative_norm_le {h t : ℝ} {Z : RestartCenterState}
    (HD : DifferentiableAt ℝ
      (fun W => restartRadialNorm (restartSectionCenterFlow h t W) - restartSectionRadius h 0 W) Z) :
    DifferentiableAt ℝ (restartSectionRadialError h t) Z ∧
      ‖fderiv ℝ (restartSectionRadialError h t) Z‖ ≤
        ‖fderiv ℝ (fun W => restartRadialNorm (restartSectionCenterFlow h t W) - restartSectionRadius h 0 W) Z‖ := by
  have H : HasFDerivAt (restartSectionRadialError h t)
      ((1 / Real.sqrt 3) • fderiv ℝ
        (fun W => restartRadialNorm (restartSectionCenterFlow h t W) - restartSectionRadius h 0 W) Z) Z := by
    convert! HD.hasFDerivAt.const_mul (1 / Real.sqrt (3 : ℝ)) using 1
    ext W
    rw [restartSectionRadialError_eq]
    ring
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
  have hcoef : (1 : ℝ) / Real.sqrt 3 ≤ 1 := (div_le_iff₀ hsqrt).mpr (by simpa only [one_mul] using hsqrt1)
  refine ⟨H.differentiableAt, ?_⟩
  rw [H.fderiv, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / Real.sqrt (3 : ℝ))]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef (norm_nonneg
    (fderiv ℝ (fun W => restartRadialNorm (restartSectionCenterFlow h t W) - restartSectionRadius h 0 W) Z))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartSectionRadialError_derivative :
    ∃ C ≥ (32 : ℝ), ∀ c : ℝ, 0 < c → ∃ K : ℝ, 0 < K ∧
      ∀ (h b T : ℝ) (Z : RestartCenterState),
        0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
        ‖Z‖ ≤ b / 2 → c * b ≤ restartRadialNorm Z → ∀ t ∈ Icc (0 : ℝ) T,
          DifferentiableAt ℝ (restartSectionRadialError h t) Z ∧
          ‖fderiv ℝ (restartSectionRadialError h t) Z‖ ≤
            K * (h * b + b ^ 2 * t + h * Real.exp (-2 * t)) := by
  obtain ⟨A, hA, HA⟩ := exists_restartSectionRadius_derivative_error
  obtain ⟨B, _, HB⟩ := exists_restartSectionRadiusTail_derivative_bound
  obtain ⟨D, _, HD⟩ := exists_restartSection_fastLayer_control
  let C := max A (max B D)
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hDC : D ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hA.trans hAC, ?_⟩
  intro c hc
  obtain ⟨K₁, hK₁, HK₁⟩ := HA c hc
  obtain ⟨K₂, hK₂, HK₂⟩ := HB c hc
  let K := max K₁ K₂
  have hK : 0 < K := hK₁.trans_le (le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  intro h b T Z hh hCh hb hT hCb hZ hradial t ht
  have hb0 := hb.1.le
  have Hheight (k : ℝ) (hk : k ≤ C) : k * h ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_right hk hh.le).trans hCh
  have Htime (k : ℝ) (hk : k ≤ C) : k * b * T ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk hb0) hT).trans hCb
  have Hcore := HK₁ h b T Z hh (Hheight A hAC) hb hT (Htime A hAC) hZ hradial t ht
  have Htail := HK₂ h b T Z hh (Hheight B hBC) hb hT (Htime B hBC) hZ hradial t ht
  have Hwall := (HD h b T Z hh (Hheight D hDC) hb hT (Htime D hDC) hZ t ht).2.1
  have Hsub := Hcore.1.hasFDerivAt.sub Htail.1.hasFDerivAt
  have Heq : (fun W => restartRadialNorm (restartSectionCenterFlow h t W) - restartSectionRadius h 0 W) =
      (fun W => restartSectionRadius h t W - restartSectionRadius h 0 W) - restartSectionRadiusTail h t := by
    ext W
    dsimp only [Pi.sub_apply, restartSectionRadiusTail]
    ring
  have Hraw : DifferentiableAt ℝ
      (fun W => restartRadialNorm (restartSectionCenterFlow h t W) - restartSectionRadius h 0 W) Z := by
    rw [Heq]
    exact Hsub.differentiableAt
  have Hnorm := restartSectionRadialError_derivative_norm_le Hraw
  refine ⟨Hnorm.1, Hnorm.2.trans ?_⟩
  rw [Heq, Hsub.fderiv]
  calc
    _ ≤ ‖fderiv ℝ (fun W => restartSectionRadius h t W - restartSectionRadius h 0 W) Z‖ +
        ‖fderiv ℝ (restartSectionRadiusTail h t) Z‖ := norm_sub_le _ _
    _ ≤ K₁ * (h * b + b ^ 2 * t) + K₂ * restartSectionStrongWall h t Z := add_le_add Hcore.2 Htail.2
    _ ≤ K₁ * (h * b + b ^ 2 * t) + K₂ * (h * Real.exp (-2 * t)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left Hwall hK₂.le)
    _ ≤ K * (h * b + b ^ 2 * t) + K * (h * Real.exp (-2 * t)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity [ht.1]))
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartSection_radial_cutoff_derivative :
    ∃ C ≥ (32 : ℝ), ∀ (c₀ C₀ : ℝ), 0 < c₀ → 0 < C₀ → ∃ K : ℝ, 0 < K ∧
      ∀ (h ρ q : ℝ), 0 < h → C * h ≤ 1 / 4 → (0 < ρ ∧ ρ ≤ 1) → 0 ≤ q →
        2 * C₀ * ρ ≤ 1 / 16 → C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ)) ≤ 1 / 8 →
        ∀ Z : RestartCenterState, ‖Z‖ ≤ C₀ * ρ → c₀ * ρ ≤ restartRadialNorm Z →
          let T := q / 2 * Real.log (1 / ρ)
          DifferentiableAt ℝ (restartSectionRadialError h T) Z ∧
          ‖fderiv ℝ (restartSectionRadialError h T) Z‖ ≤ K * (h * ρ + ρ ^ 2 * T + h * ρ ^ q) := by
  obtain ⟨C, hC, HC⟩ := exists_restartSectionRadialError_derivative
  refine ⟨C, hC, ?_⟩
  intro c₀ C₀ hc₀ hC₀
  obtain ⟨L, hL, HL⟩ := HC (c₀ / (2 * C₀)) (by positivity)
  let M := 2 * C₀ + 4 * C₀ ^ 2 + 1
  let K := L * M
  have hK : 0 < K := by dsimp only [K, M]; positivity
  refine ⟨K, hK, ?_⟩
  intro h ρ q hh hCh hρ hq hb hCb Z hZ hlower
  have hρ0 := hρ.1
  let b := 2 * C₀ * ρ
  let T := q / 2 * Real.log (1 / ρ)
  have hb0 : 0 < b := by dsimp only [b]; positivity
  have hT : 0 ≤ T := mul_nonneg (div_nonneg hq (by norm_num))
    (Real.log_nonneg ((le_div_iff₀ hρ.1).mpr (by linarith only [hρ.2])))
  have hZb : ‖Z‖ ≤ b / 2 := by dsimp only [b]; linarith only [hZ]
  have Hlower : c₀ / (2 * C₀) * b ≤ restartRadialNorm Z := by
    have Heq : c₀ / (2 * C₀) * b = c₀ * ρ := by dsimp only [b]; field_simp
    rwa [Heq]
  have H := HL h b T Z hh hCh ⟨hb0, hb⟩ hT hCb hZb Hlower T ⟨hT, le_rfl⟩
  have he : Real.exp (-2 * T) = ρ ^ q := by
    rw [Real.rpow_def_of_pos hρ.1]
    congr 1
    dsimp only [T]
    rw [one_div, Real.log_inv]
    ring
  refine ⟨H.1, H.2.trans ?_⟩
  rw [he]
  have H1 : L * (2 * C₀) ≤ K := by dsimp only [K, M]; nlinarith only [mul_nonneg hL.le (sq_nonneg C₀), hL]
  have H2 : L * (4 * C₀ ^ 2) ≤ K := by dsimp only [K, M]; nlinarith only [mul_pos hL hC₀, hL]
  have H3 : L ≤ K := by dsimp only [K, M]; nlinarith only [mul_pos hL hC₀, mul_nonneg hL.le (sq_nonneg C₀)]
  calc
    _ = (L * (2 * C₀)) * (h * ρ) + (L * (4 * C₀ ^ 2)) * (ρ ^ 2 * T) + L * (h * ρ ^ q) := by
      dsimp only [b]
      ring
    _ ≤ K * (h * ρ) + K * (ρ ^ 2 * T) + K * (h * ρ ^ q) :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right H1 (by positivity))
        (mul_le_mul_of_nonneg_right H2 (by positivity)))
        (mul_le_mul_of_nonneg_right H3 (by positivity))
    _ = _ := by ring

end
end

/-- Both lines of (E.11) hold on one actual domain, with a common constant chosen before q. -/
theorem solution :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ (c₀ C₀ : ℝ), 0 < c₀ → 0 < C₀ → ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 2 < q →
        ∃ ρstar : ℝ, 0 < ρstar ∧ ∀ ρ ∈ Ioc (0 : ℝ) ρstar,
          ∀ Z : RestartCenterState, ‖Z‖ ≤ C₀ * ρ → c₀ * ρ ≤ restartRadialNorm Z →
            let T := q / 2 * Real.log (1 / ρ)
            T ∈ normalizedMaxDomain (restartSectionChart h Z) 0 ∧
            DifferentiableAt ℝ (restartSectionRadialError h T) Z ∧
            |restartSectionRadialError h T Z| ≤ K * ρ ^ 2 ∧
            ‖fderiv ℝ (restartSectionRadialError h T) Z‖ ≤ K * ρ := by
  obtain ⟨hV, hhV, HV⟩ := exists_restartSection_radial_value_approximation
  obtain ⟨C, hC, HC⟩ := exists_restartSection_radial_cutoff_derivative
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  let hstar := min hV (1 / (4 * C))
  have hstarpos : 0 < hstar := lt_min hhV (by positivity)
  refine ⟨hstar, hstarpos, ?_⟩
  intro h hh c₀ C₀ hc₀ hC₀
  have hhpos := hh.1
  have hCh : C * h ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp (hh.2.trans (min_le_right _ _))
    nlinarith only [H]
  obtain ⟨KV, hKV, HVscale⟩ := HV h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ C₀ hC₀
  obtain ⟨KD, hKD, HD⟩ := HC c₀ C₀ hc₀ hC₀
  let K := max KV (KD * (2 * h + 1))
  have hK : 0 < K := hKV.trans_le (le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  intro q hq
  obtain ⟨ρV, hρV, HVρ⟩ := HVscale q hq
  have Hevent : ∀ᶠ ρ : ℝ in 𝓝[>] 0,
      ((0 < ρ ∧ ρ ≤ 1) ∧ 2 * C₀ * ρ ≤ 1 / 16 ∧
        C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ)) ≤ 1 / 8) ∧
          ρ * (q / 2 * Real.log (1 / ρ)) ≤ 1 := by
    filter_upwards [eventually_restart_cutoff_budget C C₀ q,
      eventually_restart_cutoff_budget 1 1 q] with ρ H₁ H₂
    exact ⟨H₁, by nlinarith only [H₂.2.2]⟩
  obtain ⟨ρD, hρD, HDρ⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp Hevent
  refine ⟨min ρV ρD, lt_min hρV hρD, ?_⟩
  intro ρ hρ Z hZ hlower
  have HVZ := HVρ ρ ⟨hρ.1, hρ.2.trans (min_le_left _ _)⟩ Z hZ
  have Hb := HDρ ⟨hρ.1, hρ.2.trans (min_le_right _ _)⟩
  have HDR := HD h ρ q hhpos hCh Hb.1.1 (by linarith only [hq]) Hb.1.2.1 Hb.1.2.2 Z hZ hlower
  refine ⟨HVZ.1, HDR.1, ?_, ?_⟩
  · exact HVZ.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg ρ))
  · have Hpower : ρ ^ q ≤ ρ := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge Hb.1.1.1 Hb.1.1.2
        (by linarith only [hq] : (1 : ℝ) ≤ q)
    have Htime : ρ ^ 2 * (q / 2 * Real.log (1 / ρ)) ≤ ρ := by
      nlinarith only [mul_le_mul_of_nonneg_right Hb.2 hρ.1.le]
    apply HDR.2.trans
    calc
      _ ≤ KD * ((2 * h + 1) * ρ) := mul_le_mul_of_nonneg_left (by
        nlinarith only [Htime, mul_le_mul_of_nonneg_left Hpower hhpos.le]) hKD.le
      _ = (KD * (2 * h + 1)) * ρ := by ring
      _ ≤ K * ρ := mul_le_mul_of_nonneg_right (le_max_right _ _) hρ.1.le
