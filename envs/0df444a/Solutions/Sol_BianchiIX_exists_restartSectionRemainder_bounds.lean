-- Prove2me | solution 1 for BianchiIX.exists_restartSectionRemainder_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:42:54.280951+00:00
-- url     : https://prove2.me/submissions/e4b96e6a-6ea0-4b30-951c-f684e34ff2fc

import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiff_normalizedField
import Theorems.Thm_BianchiIX_exists_restartSectionMixedFlow_derivative
import Theorems.Thm_BianchiIX_hasDerivAt_normalizedFlowDifferential
import Theorems.Thm_BianchiIX_hasDerivAt_normalized_components
import Theorems.Thm_BianchiIX_le_exp_of_clock_deriv_le
import Theorems.Thm_BianchiIX_norm_le_exp_of_norm_deriv_clock
import Theorems.Thm_BianchiIX_norm_le_exp_of_norm_deriv_clock_forcing
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxCurve_wall_sign
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_wall_formula
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
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
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.norm_le_quadratic_of_radial_fderiv {f : E → F} {x : E} {A B : ℝ}
    (hzero : f 0 = 0)
    (hf : ∀ θ ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ f (θ • x))
    (hbound : ∀ θ ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ f (θ • x)‖ ≤ A * θ * ‖x‖ + B) :
    ‖f x‖ ≤ A / 2 * ‖x‖ ^ 2 + B * ‖x‖ := by
  let g := fun θ : ℝ => f (θ • x)
  let R := fun θ : ℝ => A / 2 * θ ^ 2 * ‖x‖ ^ 2 + B * θ * ‖x‖
  have hg (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      HasDerivAt g (fderiv ℝ f (θ • x) x) θ := by
    convert! (hf θ hθ).hasFDerivAt.comp_hasDerivAt θ ((hasDerivAt_id' θ).smul_const x) using 1
    simp only [one_smul]
  have hR (θ : ℝ) : HasDerivAt R ((A * θ * ‖x‖ + B) * ‖x‖) θ := by
    convert! ((((hasDerivAt_id' θ).pow 2).const_mul (A / 2)).mul_const (‖x‖ ^ 2)).add
      (((hasDerivAt_id' θ).const_mul B).mul_const ‖x‖) using 1
    ring
  have H := image_norm_le_of_norm_deriv_right_le_deriv_boundary (HasDerivAt.continuousOn hg)
    (fun θ hθ => (hg θ (Ico_subset_Icc_self hθ)).hasDerivWithinAt)
    (by simp [g, R, hzero] : ‖g 0‖ ≤ R 0) hR
    (fun θ hθ => ((fderiv ℝ f (θ • x)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hbound θ (Ico_subset_Icc_self hθ)) (norm_nonneg x)))
    (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
  simpa only [g, R, one_smul, one_pow, mul_one] using H

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
open Filter
open scoped Topology
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem BianchiIX.fderiv2_comp_apply {f : E → F} {g : F → G} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g (f x)) (v w : E) :
    fderiv ℝ (fderiv ℝ (g ∘ f)) x v w =
      fderiv ℝ g (f x) (fderiv ℝ (fderiv ℝ f) x v w) +
        fderiv ℝ (fderiv ℝ g) (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) := by
  have hf' := (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hg' := (hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hcomp := ((hg.comp x hf).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have heq : (fun y => fderiv ℝ (g ∘ f) y w) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ g (f y) (fderiv ℝ f y w)) := by
    filter_upwards [hf.eventually (by norm_num), hf.continuousAt.eventually (hg.eventually (by norm_num))]
      with y hfy hgy
    rw [fderiv_comp y (hgy.differentiableAt (by norm_num)) (hfy.differentiableAt (by norm_num))]
    rfl
  have Hleft := hcomp.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have Hright := (hg'.hasFDerivAt.comp x (hf.differentiableAt (by norm_num)).hasFDerivAt).clm_apply
    (hf'.hasFDerivAt.clm_apply (hasFDerivAt_const w x))
  have H := congrArg (fun L : E →L[ℝ] G => L v) (Hleft.unique (Hright.congr_of_eventuallyEq heq))
  simpa using H

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem BianchiIX.fderiv2_clm_comp_apply {f : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (L : F →L[ℝ] G) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => L (f y))) x v w =
      L (fderiv ℝ (fderiv ℝ f) x v w) := by
  have H := fderiv2_comp_apply hf L.contDiff.contDiffAt v w
  have hL : fderiv ℝ (L : F → G) = fun _ => L := funext (fun _ => L.fderiv)
  simpa only [hL, fderiv_const_apply, zero_apply, add_zero, Function.comp_def] using H

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
open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.hasDerivAt_parametric_first_variation {Φ : E × ℝ → F} {f : ℝ × F → F} {x : E} {t : ℝ}
    (hΦ : ContDiffAt ℝ 2 Φ (x, t)) (hf : DifferentiableAt ℝ f (t, Φ (x, t)))
    (hode : (fun p => fderiv ℝ Φ p (0, 1)) =ᶠ[𝓝 (x, t)] (fun p => f (p.2, Φ p))) (v : E) :
    HasDerivAt (fun s => fderiv ℝ Φ (x, s) (v, 0))
      (fderiv ℝ (fun z => f (t, z)) (Φ (x, t)) (fderiv ℝ Φ (x, t) (v, 0))) t := by
  have hD := (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hleft := hD.hasFDerivAt.clm_apply (hasFDerivAt_const (0, 1) (x, t))
  have hright := hf.hasFDerivAt.comp (x, t)
    (hasFDerivAt_snd.prodMk (hΦ.differentiableAt (by norm_num)).hasFDerivAt)
  have heq := congrArg (fun L : (E × ℝ) →L[ℝ] F => L (v, 0))
    ((hleft.congr_of_eventuallyEq hode.symm).unique hright)
  have hslice := hf.hasFDerivAt.comp (Φ (x, t))
    ((hasFDerivAt_const t (Φ (x, t))).prodMk (hasFDerivAt_id (Φ (x, t))))
  change HasFDerivAt (fun z => f (t, z)) _ (Φ (x, t)) at hslice
  have hpath : HasDerivAt (fun s : ℝ => (x, s)) (0, 1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  have H := hasDerivAt_fderiv_apply_const hD hpath (v, 0)
  apply H.congr_deriv
  rw [(hΦ.isSymmSndFDerivAt (by norm_num)).eq (0, 1) (v, 0), hslice.fderiv]
  simpa using heq

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartCenterTransfer_apply (n : ℝ) (v : RestartCenterState) :
    restartCenterTransfer n v = ![
      restartShearFactor n * v 0 + restartShearCoupling n * (v 1 - v 2),
      restartWallFactor n * v 1, restartWallFactor n * v 2] := by
  ext i
  fin_cases i <;> rfl

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

private theorem BianchiIX.restartCenterTransfer_sub_id_bound {n : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16) :
    ‖restartCenterTransfer n - ContinuousLinearMap.id ℝ RestartCenterState‖ ≤ 3 * n := by
  obtain ⟨ha0, ha1, hc0, hc1, hk0, hk1⟩ := restart_coefficients_small hn
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [hn.1])
  intro v
  have hv (i : Fin 3) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hdiff : |v 1 - v 2| ≤ 2 * ‖v‖ := by
    have H := abs_sub_le (v 1) 0 (v 2)
    simp only [sub_zero, zero_sub, abs_neg] at H
    linarith only [H, hv 1, hv 2]
  have hw (i : Fin 3) : |(restartWallFactor n - 1) * v i| ≤ n * ‖v‖ := by
    rw [abs_mul, abs_of_nonneg hc0]
    exact mul_le_mul hc1 (hv i) (abs_nonneg _) hn.1
  apply (pi_norm_le_iff_of_nonneg (by positivity [hn.1] : 0 ≤ 3 * n * ‖v‖)).mpr
  intro i
  rw [sub_apply, ContinuousLinearMap.id_apply, restartCenterTransfer_apply]
  fin_cases i
  · change |restartShearFactor n * v 0 + restartShearCoupling n * (v 1 - v 2) - v 0| ≤ _
    rw [show restartShearFactor n * v 0 + restartShearCoupling n * (v 1 - v 2) - v 0 =
      (restartShearFactor n - 1) * v 0 + restartShearCoupling n * (v 1 - v 2) by ring]
    calc
      _ ≤ |(restartShearFactor n - 1) * v 0| + |restartShearCoupling n * (v 1 - v 2)| := abs_add_le _ _
      _ ≤ n * ‖v‖ + n * (2 * ‖v‖) := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hk0]
        exact add_le_add (mul_le_mul ha1 (hv 0) (abs_nonneg _) hn.1)
          (mul_le_mul hk1 hdiff (abs_nonneg _) hn.1)
      _ = _ := by ring
  · change |restartWallFactor n * v 1 - v 1| ≤ _
    rw [← sub_one_mul]
    exact (hw 1).trans (by nlinarith only [mul_nonneg hn.1 (norm_nonneg v)])
  · change |restartWallFactor n * v 2 - v 2| ≤ _
    rw [← sub_one_mul]
    exact (hw 2).trans (by nlinarith only [mul_nonneg hn.1 (norm_nonneg v)])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartCenterTransfer_norm_bound {n : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16) :
    ‖restartCenterTransfer n‖ ≤ 1 + 3 * n := by
  have H := norm_le_norm_sub_add (restartCenterTransfer n) (ContinuousLinearMap.id ℝ RestartCenterState)
  linarith only [H, restartCenterTransfer_sub_id_bound hn,
    ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := RestartCenterState)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartCenterTransfer_conserved_bounds {h n : ℝ}
    (hh : 0 ≤ h ∧ h ≤ 1 / 16) (hn : 0 ≤ n ∧ n ≤ 1 / 16)
    (Y : RestartCenterState →L[ℝ] RestartCenterState)
    (hY : (restartCenterTransfer n).comp Y = restartCenterTransfer h) :
    ‖Y‖ ≤ 2 ∧ ‖Y - restartCenterTransfer h‖ ≤ 6 * n := by
  have hid : Y - restartCenterTransfer h =
      (ContinuousLinearMap.id ℝ RestartCenterState - restartCenterTransfer n).comp Y := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp, hY]
  have htail : ‖Y - restartCenterTransfer h‖ ≤ 3 * n * ‖Y‖ := by
    rw [hid]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    rw [norm_sub_rev]
    exact mul_le_mul_of_nonneg_right (restartCenterTransfer_sub_id_bound hn) (norm_nonneg Y)
  have hnorm : ‖Y‖ ≤ 2 := by
    have H := norm_le_norm_sub_add Y (restartCenterTransfer h)
    have HB := restartCenterTransfer_norm_bound hh
    have Hn := mul_le_mul_of_nonneg_right hn.2 (norm_nonneg Y)
    nlinarith only [H, HB, htail, hh.2, Hn]
  exact ⟨hnorm, htail.trans (by nlinarith only [mul_le_mul_of_nonneg_left hnorm hn.1])⟩

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
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem BianchiIX.composition_second_derivative_bounds {f : E → F} {g : F → G} {x : E} {A B K : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g (f x))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hf1 : ‖fderiv ℝ f x‖ ≤ K) (hf2 : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ K)
    (hg1 : ‖fderiv ℝ g (f x)‖ ≤ A) (hg2 : ‖fderiv ℝ (fderiv ℝ g) (f x)‖ ≤ B) :
    ‖fderiv ℝ (g ∘ f) x‖ ≤ A * K ∧
      ‖fderiv ℝ (fderiv ℝ (g ∘ f)) x‖ ≤ A * K + B * K ^ 2 := by
  have hf1' (v : E) : ‖fderiv ℝ f x v‖ ≤ K * ‖v‖ :=
    ((fderiv ℝ f x).le_opNorm v).trans (mul_le_mul_of_nonneg_right hf1 (norm_nonneg v))
  have hf2' (v w : E) : ‖fderiv ℝ (fderiv ℝ f) x v w‖ ≤ K * ‖v‖ * ‖w‖ :=
    (((fderiv ℝ (fderiv ℝ f) x) v).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ f) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hf2 (norm_nonneg v))) (norm_nonneg w))
  constructor
  · rw [fderiv_comp x (hg.differentiableAt (by norm_num)) (hf.differentiableAt (by norm_num))]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hg1 hf1 (norm_nonneg _) hA)
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    rw [fderiv2_comp_apply hf hg]
    have H1 := ((fderiv ℝ g (f x)).le_opNorm (fderiv ℝ (fderiv ℝ f) x v w)).trans
      (mul_le_mul hg1 (hf2' v w) (norm_nonneg _) hA)
    let L := fderiv ℝ (fderiv ℝ g) (f x)
    have H2 := ((L (fderiv ℝ f x v)).le_opNorm (fderiv ℝ f x w)).trans
      (mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _))
    have H3 := mul_le_mul (mul_le_mul hg2 (hf1' v) (norm_nonneg _) hB)
      (hf1' w) (norm_nonneg _) (by positivity : 0 ≤ B * (K * ‖v‖))
    have Hsum := norm_add_le (fderiv ℝ g (f x) (fderiv ℝ (fderiv ℝ f) x v w))
      (L (fderiv ℝ f x v) (fderiv ℝ f x w))
    dsimp only [L] at H2 Hsum
    nlinarith only [H1, H2, H3, Hsum]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.homogeneous_solution_eq_exp_integral {I : Set ℝ} (hI : Convex ℝ I) (hopen : IsOpen I)
    {f a : ℝ → ℝ} (ha : ContinuousOn a I)
    (hf : ∀ t ∈ I, HasDerivAt f (a t * f t) t) {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    f t = f t₀ * Real.exp (∫ u in t₀..t, a u) := by
  let P : ℝ → ℝ := fun v => ∫ u in t₀..v, a u
  have hP (v : ℝ) (hv : v ∈ I) : HasDerivAt P (a v) v :=
    intervalIntegral.integral_hasDerivAt_right
      (ha.mono (hI.ordConnected.uIcc_subset ht₀ hv)).intervalIntegrable
      (ContinuousOn.stronglyMeasurableAtFilter hopen ha v hv)
      (ha.continuousAt (hopen.mem_nhds hv))
  have hF (v : ℝ) (hv : v ∈ I) :
      HasDerivAt (fun u => f u * Real.exp (-P u)) 0 v := by
    convert! (hf v hv).mul (hP v hv).neg.exp using 1
    ring
  have H := hI.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v hv => (hF v hv).hasDerivWithinAt) (C := 0) (fun _ _ => by simp) ht₀ ht
  have heq : f t * Real.exp (-P t) = f t₀ := by
    simpa [P, sub_eq_zero] using H
  calc
    f t = (f t * Real.exp (-P t)) * Real.exp (P t) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = f t₀ * Real.exp (P t) := by rw [heq]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.normalized_wall_pos {I : Set ℝ} (hI : Convex ℝ I) (hopen : IsOpen I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) (i : Fin 3) (hpos : 0 < wallValue i (α t₀)) :
    0 < wallValue i (α t) := by
  rw [normalized_wall_formula hI hopen hα ht₀ ht i]
  exact mul_pos hpos (Real.exp_pos _)

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

private theorem BianchiIX.contDiff_restartExpCoordinates (k : WithTop ℕ∞) : ContDiff ℝ k restartExpCoordinates := by
  rw [contDiff_pi]
  intro i
  fin_cases i <;> dsimp [restartExpCoordinates] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartMixedField {y : RestartState}
    (hy : 0 < restartRadicand (restartExpCoordinates y)) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartMixedField y :=
  (contDiffAt_restartCompactField hy k).comp y (contDiff_restartExpCoordinates k).contDiffAt

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

private theorem BianchiIX.restartMixedField_coordinates {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) (hn : 0 < x 2) :
    restartMixedField (restartMixedCoordinates x) =
      ![rateOne (x 0) (x 1), shearMinus (x 1) (x 2) (x 3) (x 4),
        rateTwo (x 0) (x 1) * x 3, rateThree (x 0) (x 1) * x 4] := by
  have hroot := restart_negative_branch_root hc hp
  have hq : curvature (x 2) (x 3) (x 4) = 1 - shearSq (x 0) (x 1) := by
    dsimp only [stateConstraint, constraint] at hc
    linarith only [hc]
  ext i
  fin_cases i <;>
    simp [restartMixedField, restartMixedCoordinates, restartExpCoordinates, restartCompactField,
      restartCompactWeakRate, restartCompactRoot, restartRadicand, Real.exp_log hn] <;>
    rw [← hroot, hq] <;> dsimp only [rateOne, rateTwo, rateThree] <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartMixedCoordinates {x : ℝ → NormalizedState} {t : ℝ}
    (hx : HasDerivAt x (normalizedField (x t)) t) (hc : stateConstraint (x t) = 1)
    (hp : x t 0 < 0) (hn : 0 < x t 2) :
    HasDerivAt (fun r => restartMixedCoordinates (x r))
      (restartMixedField (restartMixedCoordinates (x t))) t := by
  rw [restartMixedField_coordinates hc hp hn]
  obtain ⟨_, hs, hN, ha, hb⟩ := hasDerivAt_normalized_components hx
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivAt (fun r => Real.log (x r 2)) (rateOne (x t 0) (x t 1)) t
    convert! hN.log hn.ne' using 1
    simp only [mul_div_cancel_right₀ _ hn.ne']
  · exact hs
  · exact ha
  · exact hb

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
open Set Filter
open scoped Topology

private theorem BianchiIX.restart_reference_linear_conservation {I : Set ℝ} (hI : Convex ℝ I)
    {n s a b : ℝ → ℝ} (hn₀ : ∀ t ∈ I, n t ^ 2 < 1)
    (hn : ∀ t ∈ I, HasDerivAt n (n t * restartReferenceStrongRate (n t)) t)
    (hs : ∀ t ∈ I, HasDerivAt s (n t ^ 2 * s t + Real.sqrt 3 * n t * (a t - b t)) t)
    (ha : ∀ t ∈ I, HasDerivAt a (restartReferenceWallRate (n t) * a t) t)
    (hb : ∀ t ∈ I, HasDerivAt b (restartReferenceWallRate (n t) * b t) t)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    restartShearFactor (n t) * s t + restartShearCoupling (n t) * (a t - b t) =
        restartShearFactor (n t₀) * s t₀ + restartShearCoupling (n t₀) * (a t₀ - b t₀) ∧
      restartWallFactor (n t) * a t = restartWallFactor (n t₀) * a t₀ ∧
      restartWallFactor (n t) * b t = restartWallFactor (n t₀) * b t₀ := by
  have Hconst {f : ℝ → ℝ} (hf : ∀ r ∈ I, HasDerivAt f 0 r) : f t = f t₀ := by
    have H := hI.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r hr => (hf r hr).hasDerivWithinAt) (C := 0) (fun _ _ => by simp) ht₀ ht
    simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using H
  have Hwall {w : ℝ → ℝ}
      (hw : ∀ r ∈ I, HasDerivAt w (restartReferenceWallRate (n r) * w r) r) :
      restartWallFactor (n t) * w t = restartWallFactor (n t₀) * w t₀ := by
    apply Hconst
    intro r hr
    have HC := (hasDerivAt_restartWallFactor (hn₀ r hr)).differentiableAt.hasDerivAt.comp r (hn r hr)
    have HC0 := (restart_transport_cancellation (hn₀ r hr)).2.1
    convert! HC.mul (hw r hr) using 1
    simp only [Function.comp_def]
    linear_combination -(w r) * HC0
  refine ⟨?_, Hwall ha, Hwall hb⟩
  apply Hconst
  intro r hr
  have HV : HasDerivAt (fun q => a q - b q)
      (restartReferenceWallRate (n r) * (a r - b r) + 0) r := by
    convert! (ha r hr).sub (hb r hr) using 1
    ring
  have H := (hasDerivAt_restart_transported_components (dF := 0) (es := 0) (ev := 0)
    (hn₀ r hr) (by simpa only [add_zero] using hn r hr)
    (by simpa only [add_zero] using hs r hr) HV).1
  simpa only [mul_zero, zero_mul, zero_add, add_zero] using H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasFDerivAt_restartExpCoordinates (y : RestartState) :
    HasFDerivAt restartExpCoordinates (restartExpDifferential (Real.exp (y 0))) y := by
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · exact (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) y).exp
  · exact hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) y
  · exact hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) y
  · exact hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) y

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartExpCoordinates_fderiv (y v : RestartState) :
    fderiv ℝ restartExpCoordinates y v = ![Real.exp (y 0) * v 0, v 1, v 2, v 3] := by
  rw [(hasFDerivAt_restartExpCoordinates y).fderiv]
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartExpCoordinates_fderiv2 (y v w : RestartState) :
    fderiv ℝ (fderiv ℝ restartExpCoordinates) y v w =
      ![Real.exp (y 0) * v 0 * w 0, 0, 0, 0] := by
  have hp (i : Fin 4) : fderiv ℝ (fun z : RestartState => z i) = fun _ => ContinuousLinearMap.proj i :=
    funext (fun z => (hasFDerivAt_apply (𝕜 := ℝ) i z).fderiv)
  have he : fderiv ℝ (fun z : RestartState => Real.exp (z 0)) =
      fun z => Real.exp (z 0) • (ContinuousLinearMap.proj 0 : RestartState →L[ℝ] ℝ) :=
    funext (fun z => (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) z).exp.fderiv)
  have he2 : fderiv ℝ (fderiv ℝ (fun z : RestartState => Real.exp (z 0))) y v w =
      Real.exp (y 0) * v 0 * w 0 := by
    rw [he, (((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) y).exp).smul_const
      (ContinuousLinearMap.proj 0 : RestartState →L[ℝ] ℝ)).fderiv]
    rfl
  have H (i : Fin 4) := fderiv2_clm_comp_apply (x := y) (contDiff_restartExpCoordinates 2).contDiffAt
    (ContinuousLinearMap.proj i) v w
  ext i
  fin_cases i
  · have H0 := H 0
    change fderiv ℝ (fderiv ℝ (fun z : RestartState => Real.exp (z 0))) y v w = _ at H0
    exact (he2.symm.trans H0).symm
  · have H1 := H 1
    change fderiv ℝ (fderiv ℝ (fun z : RestartState => z 1)) y v w = _ at H1
    rw [hp, fderiv_const_apply] at H1
    exact H1.symm
  · have H2 := H 2
    change fderiv ℝ (fderiv ℝ (fun z : RestartState => z 2)) y v w = _ at H2
    rw [hp, fderiv_const_apply] at H2
    exact H2.symm
  · have H3 := H 3
    change fderiv ℝ (fderiv ℝ (fun z : RestartState => z 3)) y v w = _ at H3
    rw [hp, fderiv_const_apply] at H3
    exact H3.symm

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartExpCoordinates_derivative_bounds {y : RestartState} (hy : Real.exp (y 0) ≤ 1) :
    ‖fderiv ℝ restartExpCoordinates y‖ ≤ 1 ∧
      ‖fderiv ℝ (fderiv ℝ restartExpCoordinates) y‖ ≤ 1 := by
  have hv (v : RestartState) (i : Fin 4) : |v i| ≤ ‖v‖ := norm_le_pi_norm v i
  have hn : 0 ≤ Real.exp (y 0) := (Real.exp_pos _).le
  have hfirst (v : RestartState) : |Real.exp (y 0) * v 0| ≤ ‖v‖ := by
    rw [abs_mul, abs_of_nonneg hn]
    exact (mul_le_mul_of_nonneg_left (hv v 0) hn).trans (mul_le_of_le_one_left (norm_nonneg v) hy)
  constructor
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    rw [one_mul, restartExpCoordinates_fderiv]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i
    fin_cases i
    · exact hfirst v
    · exact hv v 1
    · exact hv v 2
    · exact hv v 3
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    rw [one_mul, restartExpCoordinates_fderiv2]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg w))).mpr
    intro i
    fin_cases i
    · change |Real.exp (y 0) * v 0 * w 0| ≤ _
      rw [abs_mul]
      exact mul_le_mul (hfirst v) (hv w 0) (abs_nonneg _) (norm_nonneg v)
    all_goals simpa using mul_nonneg (norm_nonneg v) (norm_nonneg w)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_restartMixed_derivative_bounds :
    ∃ C ≥ (1 : ℝ), ∀ y : RestartState, ‖restartExpCoordinates y‖ ≤ 1 / 16 →
      ‖fderiv ℝ restartMixedField y‖ ≤ C * ‖restartExpCoordinates y‖ ∧
        ‖fderiv ℝ (fderiv ℝ restartMixedField) y‖ ≤ C := by
  obtain ⟨B, hB, HB⟩ := exists_restartCompact_derivative_bounds
  have hB0 : 0 ≤ B := by linarith only [hB]
  refine ⟨2 * B, by linarith only [hB], ?_⟩
  intro y hy
  have hn : Real.exp (y 0) ≤ 1 := by
    have H : |Real.exp (y 0)| ≤ 1 / 16 := (norm_le_pi_norm (restartExpCoordinates y) 0).trans hy
    rw [abs_of_pos (Real.exp_pos _)] at H
    linarith only [H]
  have hr : 0 < restartRadicand (restartExpCoordinates y) := by
    have H := (restartCompact_box_bounds hy).2.1
    linarith only [H]
  have H := composition_second_derivative_bounds (contDiff_restartExpCoordinates 2).contDiffAt
    (contDiffAt_restartCompactField hr 2) (mul_nonneg hB0 (norm_nonneg _)) hB0 (by norm_num : (0 : ℝ) ≤ 1)
    (restartExpCoordinates_derivative_bounds hn).1 (restartExpCoordinates_derivative_bounds hn).2
    (HB _ hy).1 (HB _ hy).2
  change ‖fderiv ℝ restartMixedField y‖ ≤ B * ‖restartExpCoordinates y‖ * 1 ∧
    ‖fderiv ℝ (fderiv ℝ restartMixedField) y‖ ≤ B * ‖restartExpCoordinates y‖ * 1 + B * 1 ^ 2 at H
  constructor
  · nlinarith only [H.1, mul_nonneg hB0 (norm_nonneg (restartExpCoordinates y))]
  · nlinarith only [H.2, mul_le_mul_of_nonneg_left hy hB0, hB0]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.convex_restartMixedBox : Convex ℝ restartMixedBox := by
  apply convex_pi
  intro i _
  split_ifs
  · exact convex_Iic _
  · exact convex_Icc _ _

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.mem_restartMixedBox_iff (y : RestartState) :
    y ∈ restartMixedBox ↔ ‖restartExpCoordinates y‖ ≤ 1 / 16 := by
  have hlog : y 0 ≤ Real.log (1 / 16) ↔ Real.exp (y 0) ≤ 1 / 16 :=
    Real.le_log_iff_exp_le (by norm_num)
  constructor
  · intro hy
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16)).mpr
    intro i
    have H := hy i (Set.mem_univ i)
    fin_cases i
    · change y 0 ≤ Real.log (1 / 16) at H
      change |Real.exp (y 0)| ≤ 1 / 16
      rw [abs_of_pos (Real.exp_pos _)]
      exact hlog.mp H
    · exact abs_le.mpr H
    · exact abs_le.mpr H
    · exact abs_le.mpr H
  · intro hy i _
    have H := (norm_le_pi_norm (restartExpCoordinates y) i).trans hy
    fin_cases i
    · change y 0 ≤ Real.log (1 / 16)
      apply hlog.mpr
      change |Real.exp (y 0)| ≤ 1 / 16 at H
      simpa only [abs_of_pos (Real.exp_pos _)] using H
    · exact abs_le.mp H
    · exact abs_le.mp H
    · exact abs_le.mp H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_restartMixed_uniform_bounds :
    ∃ C ≥ (1 : ℝ),
      (∀ y : RestartState, ‖restartExpCoordinates y‖ ≤ 1 / 16 →
        ‖fderiv ℝ restartMixedField y‖ ≤ C * ‖restartExpCoordinates y‖ ∧
          ‖fderiv ℝ (fderiv ℝ restartMixedField) y‖ ≤ C) ∧
      (∀ y z : RestartState, ‖restartExpCoordinates y‖ ≤ 1 / 16 →
        ‖restartExpCoordinates z‖ ≤ 1 / 16 →
        ‖fderiv ℝ restartMixedField y - fderiv ℝ restartMixedField z‖ ≤ C * ‖y - z‖) := by
  obtain ⟨C, hC, HC⟩ := exists_restartMixed_derivative_bounds
  refine ⟨C, hC, HC, ?_⟩
  intro y z hy hz
  have hdiff (x : RestartState) (hx : x ∈ restartMixedBox) :
      DifferentiableAt ℝ (fderiv ℝ restartMixedField) x := by
    have H := (restartCompact_box_bounds ((mem_restartMixedBox_iff x).mp hx)).2.1
    exact ((contDiffAt_restartMixedField (by linarith only [H]) 2).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hbound (x : RestartState) (hx : x ∈ restartMixedBox) :
      ‖fderiv ℝ (fderiv ℝ restartMixedField) x‖ ≤ C := (HC x ((mem_restartMixedBox_iff x).mp hx)).2
  exact Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound convex_restartMixedBox
    ((mem_restartMixedBox_iff z).mpr hz) ((mem_restartMixedBox_iff y).mpr hy)

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal

private theorem BianchiIX.hasFDerivAt_normalizedField (x : NormalizedState) :
    HasFDerivAt normalizedField (normalizedDifferential x) x :=
  ((contDiff_normalizedField 1).differentiable (by norm_num) x).hasFDerivAt

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
open scoped Topology

private theorem BianchiIX.normalizedFlowDifferential_initial (x : NormalizedState) (t₀ : ℝ) :
    normalizedFlowDifferential x t₀ t₀ = ContinuousLinearMap.id ℝ NormalizedState := by
  simp [normalizedFlowDifferential, normalizedMaxCurve_initial]

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
open Set Filter
open scoped Topology

private theorem BianchiIX.restartReferenceInitial_constraint {h : ℝ} (hh : h ^ 2 ≤ 1) :
    stateConstraint (restartReferenceInitial h) = 1 := by
  change (-restartReferenceRoot h) ^ 2 + 0 ^ 2 + curvature h 0 0 = 1
  simp [curvature, restartReferenceRoot_sq hh]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartReferenceCurve_initial (h : ℝ) : restartReferenceCurve h 0 = restartReferenceInitial h :=
  normalizedMaxCurve_initial _ _

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartReferenceCurve_center_zero (h : ℝ) {t : ℝ}
    (ht : t ∈ normalizedMaxDomain (restartReferenceInitial h) 0) :
    restartReferenceCurve h t 1 = 0 ∧ restartReferenceCurve h t 3 = 0 ∧ restartReferenceCurve h t 4 = 0 := by
  let S := maximalNormalizedSolution (restartReferenceInitial h) 0
  have Hw (r : ℝ) (hr : r ∈ S.domain) : S.curve r 3 = 0 ∧ S.curve r 4 = 0 := by
    have H₁ := normalized_wall_formula S.convex_domain S.isOpen_domain S.hasDerivAt S.initial_mem hr 1
    have H₂ := normalized_wall_formula S.convex_domain S.isOpen_domain S.hasDerivAt S.initial_mem hr 2
    rw [S.initial_eq] at H₁ H₂
    simpa [wallValue, restartReferenceInitial] using And.intro H₁ H₂
  have Hs (r : ℝ) (hr : r ∈ S.domain) :
      HasDerivAt (fun q => S.curve q 1) (S.curve r 2 ^ 2 * S.curve r 1) r := by
    simpa [normalizedField, shearMinus, curvature, (Hw r hr).1, (Hw r hr).2] using
      hasDerivAt_pi.mp (S.hasDerivAt r hr) 1
  have H := homogeneous_solution_eq_exp_integral S.convex_domain S.isOpen_domain
    ((continuous_apply 2).comp_continuousOn (HasDerivAt.continuousOn S.hasDerivAt) |>.pow 2)
    Hs S.initial_mem ht
  rw [S.initial_eq] at H
  refine ⟨?_, (Hw t ht).1, (Hw t ht).2⟩
  change S.curve t 1 = 0
  simpa [restartReferenceInitial] using H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartReferenceCurve_forward {h t : ℝ} (hh : h ^ 2 ≤ 1) (ht : 0 ≤ t) :
    t ∈ normalizedMaxDomain (restartReferenceInitial h) 0 ∧
    HasDerivAt (restartReferenceCurve h) (normalizedField (restartReferenceCurve h t)) t ∧
    stateConstraint (restartReferenceCurve h t) = 1 := by
  have H := normalizedMaxCurve_forward_of_constraint (restartReferenceInitial_constraint hh) ht
  exact ⟨normalizedMaxDomain_contains_Ici_of_constraint (restartReferenceInitial_constraint hh) 0 ht, H.1, H.2.1⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartReferenceCurve_circle {h t : ℝ} (hh : h ^ 2 ≤ 1) (ht : 0 ≤ t) :
    restartReferenceCurve h t 0 ^ 2 + restartReferenceCurve h t 2 ^ 2 = 1 := by
  have HF := restartReferenceCurve_forward hh ht
  obtain ⟨hs, ha, hb⟩ := restartReferenceCurve_center_zero h HF.1
  simpa [stateConstraint, constraint, shearSq, curvature, hs, ha, hb] using HF.2.2

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartReference_shear {h t : ℝ} (hh : h ^ 2 ≤ 1) (ht : 0 ≤ t) :
    HasDerivAt (fun r => restartReferenceCurve h r 0)
      (restartReferenceCurve h t 2 ^ 2 * (restartReferenceCurve h t 0 - 2)) t := by
  have HF := restartReferenceCurve_forward hh ht
  have Hw := restartReferenceCurve_center_zero h HF.1
  convert! hasDerivAt_pi.mp HF.2.1 0 using 1
  simp only [normalizedField, Matrix.cons_val_zero, shearPlus, curvature, Hw.2.1, Hw.2.2]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartReferenceCurve_shear_le {h t : ℝ} (hh : h ^ 2 ≤ 1) (ht : 0 ≤ t) :
    restartReferenceCurve h t 0 ≤ -restartReferenceRoot h := by
  have HD (r : ℝ) (hr : r ∈ Ici (0 : ℝ)) := hasDerivAt_restartReference_shear hh hr
  have HM : AntitoneOn (fun r => restartReferenceCurve h r 0) (Ici (0 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) (HasDerivAt.continuousOn HD)
      (fun r hr => (HD r (interior_subset hr)).differentiableAt.differentiableWithinAt)
    intro r hr
    rw [(HD r (interior_subset hr)).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
    have HC := restartReferenceCurve_circle hh (interior_subset hr)
    nlinarith only [HC, sq_nonneg (restartReferenceCurve h r 2), sq_nonneg (restartReferenceCurve h r 0 - 1)]
  have H := HM (by simp) ht ht
  simpa only [restartReferenceCurve_initial, restartReferenceInitial, Matrix.cons_val_zero] using H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartReferenceCurve_shape {h t : ℝ} (hh : h ^ 2 < 1) (ht : 0 ≤ t) :
    restartReferenceCurve h t 2 ^ 2 < 1 ∧
      restartReferenceCurve h t = restartReferenceInitial (restartReferenceCurve h t 2) := by
  have HF := restartReferenceCurve_forward hh.le ht
  have Hw := restartReferenceCurve_center_zero h HF.1
  have hp : restartReferenceCurve h t 0 < 0 :=
    (restartReferenceCurve_shear_le hh.le ht).trans_lt (neg_neg_of_pos (restartReferenceRoot_pos hh))
  have HC := restartReferenceCurve_circle hh.le ht
  refine ⟨by nlinarith only [HC, sq_pos_of_neg hp], ?_⟩
  have Hroot := restart_negative_branch_root HF.2.2 hp
  simp only [Hw.1, Hw.2.1, Hw.2.2, curvature, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, zero_mul, add_zero, sub_zero] at Hroot
  ext i
  fin_cases i
  · change restartReferenceCurve h t 0 = -restartReferenceRoot (restartReferenceCurve h t 2)
    dsimp only [restartReferenceRoot]
    linarith only [Hroot]
  · exact Hw.1
  · rfl
  · exact Hw.2.1
  · exact Hw.2.2

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartReferenceCurve_strong_pos {h t : ℝ} (hh : 0 < h) (hsmall : h ^ 2 ≤ 1) (ht : 0 ≤ t) :
    0 < restartReferenceCurve h t 2 := by
  let S := maximalNormalizedSolution (restartReferenceInitial h) 0
  apply normalized_wall_pos S.convex_domain S.isOpen_domain S.hasDerivAt S.initial_mem
    (restartReferenceCurve_forward hsmall ht).1 0
  simpa [S.initial_eq, wallValue, restartReferenceInitial] using hh

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartReferenceCurve_strong_decay {h t : ℝ} (hh : 0 < h ∧ h ≤ 1 / 16) (ht : 0 ≤ t) :
    0 < restartReferenceCurve h t 2 ∧ restartReferenceCurve h t 2 ≤ h * Real.exp (-2 * t) := by
  have hh2 : h ^ 2 < 1 := by nlinarith only [hh.1, hh.2]
  have hz : 15 / 16 ≤ restartReferenceRoot h := by
    have H := restartReferenceRoot_sq hh2.le
    have Hpos := (restartReferenceRoot_pos hh2).le
    nlinarith only [H, Hpos, hh.1, hh.2]
  have HD (r : ℝ) (hr : r ∈ Ici (0 : ℝ)) :=
    (hasDerivAt_normalized_components (restartReferenceCurve_forward hh2.le hr).2.1).2.2.1
  have HB (r : ℝ) (hr : r ∈ Ici (0 : ℝ)) :
      rateOne (restartReferenceCurve h r 0) (restartReferenceCurve h r 1) * restartReferenceCurve h r 2 ≤
        -2 * restartReferenceCurve h r 2 := by
    have Hp := restartReferenceCurve_shear_le hh2.le hr
    have Hs := (restartReferenceCurve_center_zero h (restartReferenceCurve_forward hh2.le hr).1).1
    apply mul_le_mul_of_nonneg_right _ (restartReferenceCurve_strong_pos hh.1 hh2.le hr).le
    simp only [rateOne, shearSq, Hs, zero_pow (by norm_num : 2 ≠ 0), add_zero]
    nlinarith only [Hp, hz, sq_nonneg (restartReferenceCurve h r 0 + 15 / 16)]
  have HE := le_exp_of_linear_deriv_le (convex_Ici (0 : ℝ)) HD HB (s := 0) (t := t) (by simp) ht ht
  refine ⟨restartReferenceCurve_strong_pos hh.1 hh2.le ht, ?_⟩
  simpa [restartReferenceCurve_initial, restartReferenceInitial] using HE

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartReference_strong {h t : ℝ} (hh : h ^ 2 < 1) (ht : 0 ≤ t) :
    HasDerivAt (fun r => restartReferenceCurve h r 2)
      (restartReferenceCurve h t 2 * restartReferenceStrongRate (restartReferenceCurve h t 2)) t := by
  have H := (hasDerivAt_restart_components (restartReferenceCurve_forward hh.le ht).2.1
    (restartReferenceCurve_forward hh.le ht).2.2).1
  have Hroot : restartReferenceCurve h t 0 = -restartReferenceRoot (restartReferenceCurve h t 2) :=
    congrFun (restartReferenceCurve_shape hh ht).2 0
  have Hw := restartReferenceCurve_center_zero h (restartReferenceCurve_forward hh.le ht).1
  have Hdelta : restartStrongRateDifference (restartReferenceCurve h t) = 0 := by
    simp [restartStrongRateDifference, restartCurvatureDifference, restartRootDifference, Hroot, Hw.2.1, Hw.2.2]
  simpa only [Hdelta, add_zero] using H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedDifferential_restart_reference_center {n : ℝ} (hn : n ^ 2 < 1) (d : NormalizedState) :
    normalizedDifferential (restartReferenceInitial n) d 1 = n ^ 2 * d 1 + Real.sqrt 3 * n * (d 3 - d 4) ∧
    normalizedDifferential (restartReferenceInitial n) d 3 = restartReferenceWallRate n * d 3 ∧
    normalizedDifferential (restartReferenceInitial n) d 4 = restartReferenceWallRate n * d 4 := by
  let γ : ℝ → NormalizedState := fun r => restartReferenceInitial n + r • d
  have Hγ : HasDerivAt γ d 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (restartReferenceInitial n)).add ((hasDerivAt_id' 0).smul_const d) using 1
    simp
  have Hfield : HasDerivAt (fun r => normalizedField (γ r))
      (normalizedDifferential (restartReferenceInitial n) d) 0 := by
    simpa only [Function.comp_def] using
      (hasFDerivAt_normalizedField (restartReferenceInitial n)).comp_hasDerivAt_of_eq 0 Hγ (by simp [γ])
  have hp := hasDerivAt_pi.mp Hγ 0
  have hs := hasDerivAt_pi.mp Hγ 1
  have hN := hasDerivAt_pi.mp Hγ 2
  have ha := hasDerivAt_pi.mp Hγ 3
  have hb := hasDerivAt_pi.mp Hγ 4
  have HQ := ((hN.pow 2).add (ha.pow 2) |>.add (hb.pow 2)).sub
    (((hN.mul ha).add (ha.mul hb) |>.add (hb.mul hN)).const_mul 2)
  constructor
  · apply (hasDerivAt_pi.mp Hfield 1).unique
    convert! (HQ.mul hs).add
      ((((ha.pow 2).neg.add (hb.pow 2)).add (hN.mul ha) |>.sub (hN.mul hb)).const_mul (Real.sqrt 3)) using 1
    simp [γ, restartReferenceInitial]
    ring
  constructor
  · apply (hasDerivAt_pi.mp Hfield 3).unique
    convert! (((hp.pow 2).add (hs.pow 2)).neg.sub hp |>.add (hs.const_mul (Real.sqrt 3))).mul ha using 1
    simp [γ, restartReferenceInitial, restartReferenceWallRate, restartReferenceRoot_sq hn.le]
  · apply (hasDerivAt_pi.mp Hfield 4).unique
    convert! (((hp.pow 2).add (hs.pow 2)).neg.sub hp |>.sub (hs.const_mul (Real.sqrt 3))).mul hb using 1
    simp [γ, restartReferenceInitial, restartReferenceWallRate, restartReferenceRoot_sq hn.le]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartReferenceVariation_initial (h : ℝ) (d : NormalizedState) :
    restartReferenceVariation h d 0 = d := by
  simp only [restartReferenceVariation, normalizedFlowDifferential_initial, ContinuousLinearMap.id_apply]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartReferenceVariation_center {h t : ℝ}
    (hh : h ^ 2 < 1) (ht : 0 ≤ t) (d : NormalizedState) :
    HasDerivAt (fun r => restartReferenceVariation h d r 1)
      (restartReferenceCurve h t 2 ^ 2 * restartReferenceVariation h d t 1 +
        Real.sqrt 3 * restartReferenceCurve h t 2 *
          (restartReferenceVariation h d t 3 - restartReferenceVariation h d t 4)) t ∧
    HasDerivAt (fun r => restartReferenceVariation h d r 3)
      (restartReferenceWallRate (restartReferenceCurve h t 2) * restartReferenceVariation h d t 3) t ∧
    HasDerivAt (fun r => restartReferenceVariation h d r 4)
      (restartReferenceWallRate (restartReferenceCurve h t 2) * restartReferenceVariation h d t 4) t := by
  have HD : HasDerivAt (restartReferenceVariation h d)
      (normalizedDifferential (restartReferenceCurve h t) (restartReferenceVariation h d t)) t := by
    convert!
      (hasDerivAt_normalizedFlowDifferential (restartReferenceCurve_forward hh.le ht).1).clm_apply
        (hasDerivAt_const t d) using 1
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.map_zero, add_zero]
    rfl
  have HC := normalizedDifferential_restart_reference_center (restartReferenceCurve_shape hh ht).1
    (restartReferenceVariation h d t)
  rw [← (restartReferenceCurve_shape hh ht).2] at HC
  exact ⟨(hasDerivAt_pi.mp HD 1).congr_deriv HC.1,
    (hasDerivAt_pi.mp HD 3).congr_deriv HC.2.1, (hasDerivAt_pi.mp HD 4).congr_deriv HC.2.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartReferenceVariation_conservation {h t : ℝ} (hh : h ^ 2 < 1) (ht : 0 ≤ t) (d : NormalizedState) :
    let n := restartReferenceCurve h t 2
    let v := restartReferenceVariation h d t
    restartShearFactor n * v 1 + restartShearCoupling n * (v 3 - v 4) =
        restartShearFactor h * d 1 + restartShearCoupling h * (d 3 - d 4) ∧
      restartWallFactor n * v 3 = restartWallFactor h * d 3 ∧
      restartWallFactor n * v 4 = restartWallFactor h * d 4 := by
  have HC := restart_reference_linear_conservation (I := Ici (0 : ℝ)) (convex_Ici 0)
    (fun r hr => (restartReferenceCurve_shape hh hr).1)
    (fun r hr => hasDerivAt_restartReference_strong hh hr)
    (fun r hr => (hasDerivAt_restartReferenceVariation_center hh hr d).1)
    (fun r hr => (hasDerivAt_restartReferenceVariation_center hh hr d).2.1)
    (fun r hr => (hasDerivAt_restartReferenceVariation_center hh hr d).2.2)
    (t₀ := 0) (t := t) (by simp) ht
  simpa [restartReferenceCurve_initial, restartReferenceInitial, restartReferenceVariation_initial] using HC

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionChart_zero (h : ℝ) : restartSectionChart h 0 = restartReferenceInitial h := by
  ext i
  fin_cases i <;> simp [restartSectionChart, restartSectionRadicand, restartReferenceInitial,
    restartReferenceRoot, curvature]

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
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_restartSectionChart_zero {h : ℝ} (hh : h ^ 2 < 1) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (restartSectionChart h) 0 := by
  have hr : ContDiff ℝ k (restartSectionRadicand h) := by
    unfold restartSectionRadicand curvature
    fun_prop
  have h0 : restartSectionRadicand h 0 ≠ 0 := by
    simpa [restartSectionRadicand, curvature] using (sub_pos.mpr hh).ne'
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact (hr.contDiffAt.sqrt h0).neg
  · exact contDiffAt_apply ℝ ℝ (0 : Fin 3) 0
  · exact contDiffAt_const
  · exact contDiffAt_apply ℝ ℝ (1 : Fin 3) 0
  · exact contDiffAt_apply ℝ ℝ (2 : Fin 3) 0

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartCenterProjection_section_differential {h : ℝ} (hh : h ^ 2 < 1) :
    restartCenterProjection.comp (fderiv ℝ (restartSectionChart h) 0) =
      ContinuousLinearMap.id ℝ RestartCenterState := by
  have HD := (contDiffAt_restartSectionChart_zero hh 1).differentiableAt (by norm_num)
  have H := restartCenterProjection.hasFDerivAt.comp 0 HD.hasFDerivAt
  have H' : HasFDerivAt (fun Z : RestartCenterState => Z)
      (restartCenterProjection.comp (fderiv ℝ (restartSectionChart h) 0)) 0 := by
    simpa only [Function.comp_def, restartCenterProjection_section] using H
  exact H'.unique (hasFDerivAt_id 0)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_restartSectionCenterFlow_zero {h t : ℝ} (hh : h ^ 2 < 1) (ht : 0 ≤ t) :
    HasFDerivAt (restartSectionCenterFlow h t) (restartReferenceCenterDifferential h t) 0 := by
  have HD := (contDiffAt_restartSectionChart_zero hh 1).differentiableAt (by norm_num)
  have HF := hasFDerivAt_normalizedMaxCurve_initial (restartReferenceCurve_forward hh.le ht).1
  rw [← restartSectionChart_zero h] at HF
  have H := restartCenterProjection.hasFDerivAt.comp 0 (HF.comp 0 HD.hasFDerivAt)
  rw [restartSectionChart_zero] at H
  convert! H using 1

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartReferenceCenterDifferential_conservation {h t : ℝ} (hh : h ^ 2 < 1) (ht : 0 ≤ t) :
    (restartCenterTransfer (restartReferenceCurve h t 2)).comp (restartReferenceCenterDifferential h t) =
      restartCenterTransfer h := by
  ext Z i
  let d := fderiv ℝ (restartSectionChart h) 0 Z
  have Hd : restartCenterProjection d = Z :=
    congrArg (fun L : RestartCenterState →L[ℝ] RestartCenterState => L Z)
      (restartCenterProjection_section_differential hh)
  have hds : d 1 = Z 0 := congrFun Hd 0
  have hda : d 3 = Z 1 := congrFun Hd 1
  have hdb : d 4 = Z 2 := congrFun Hd 2
  obtain ⟨Hs, Ha, Hb⟩ := restartReferenceVariation_conservation hh ht d
  simp only [hds, hda, hdb] at Hs Ha Hb
  fin_cases i
  · exact Hs
  · exact Ha
  · exact Hb

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartReferenceCenterDifferential_bounds {h t : ℝ}
    (hh : 0 < h ∧ h ≤ 1 / 16) (ht : 0 ≤ t) :
    ‖restartReferenceCenterDifferential h t‖ ≤ 2 ∧
      ‖restartReferenceCenterDifferential h t - restartCenterTransfer h‖ ≤ 6 * h * Real.exp (-2 * t) := by
  have hh2 : h ^ 2 < 1 := by nlinarith only [hh.1, hh.2]
  obtain ⟨hn0, hnexp⟩ := restartReferenceCurve_strong_decay hh ht
  have hn : restartReferenceCurve h t 2 ≤ 1 / 16 := by
    have he : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [ht])
    have H := mul_le_mul_of_nonneg_left he hh.1.le
    nlinarith only [hnexp, H, hh.2]
  obtain ⟨HY, Htail⟩ := restartCenterTransfer_conserved_bounds ⟨hh.1.le, hh.2⟩ ⟨hn0.le, hn⟩
    (restartReferenceCenterDifferential h t) (restartReferenceCenterDifferential_conservation hh2 ht)
  exact ⟨HY, Htail.trans (by nlinarith only [hnexp])⟩

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

private theorem BianchiIX.restartMixedChart_constraint {y : RestartState}
    (hy : 0 ≤ restartRadicand (restartExpCoordinates y)) :
    stateConstraint (restartMixedChart y) = 1 := by
  have H := Real.sq_sqrt hy
  dsimp [stateConstraint, constraint, shearSq, restartMixedChart, restartCompactRoot]
  rw [neg_sq, H]
  dsimp [restartRadicand, restartExpCoordinates]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartMixedCoordinates_chart (y : RestartState) :
    restartMixedCoordinates (restartMixedChart y) = y := by
  ext i
  fin_cases i <;> simp [restartMixedCoordinates, restartMixedChart, Real.log_exp]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartExpCoordinates_mixed {x : NormalizedState} (hn : 0 < x 2) :
    restartExpCoordinates (restartMixedCoordinates x) = restartPhysicalCoordinates x := by
  ext i
  fin_cases i <;> simp [restartExpCoordinates, restartMixedCoordinates,
    restartPhysicalCoordinates, Real.exp_log hn]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartMixedFlow_initial (y : RestartState) : restartMixedFlow (y, 0) = y := by
  rw [restartMixedFlow, normalizedMaxCurve_initial, restartMixedCoordinates_chart]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_restartMixedChart {y : RestartState}
    (hy : 0 < restartRadicand (restartExpCoordinates y)) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartMixedChart y := by
  have hr := (contDiffAt_restartCompactRoot hy k).comp y (contDiff_restartExpCoordinates k).contDiffAt
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact hr.neg
  · exact contDiffAt_apply ℝ ℝ (1 : Fin 4) y
  · exact (contDiffAt_apply ℝ ℝ (0 : Fin 4) y).exp
  · exact contDiffAt_apply ℝ ℝ (2 : Fin 4) y
  · exact contDiffAt_apply ℝ ℝ (3 : Fin 4) y

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_restartMixedCoordinates {x : NormalizedState} (hn : x 2 ≠ 0)
    (k : WithTop ℕ∞) : ContDiffAt ℝ k restartMixedCoordinates x := by
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact (contDiffAt_apply ℝ ℝ (2 : Fin 5) x).log hn
  · exact contDiffAt_apply ℝ ℝ (1 : Fin 5) x
  · exact contDiffAt_apply ℝ ℝ (3 : Fin 5) x
  · exact contDiffAt_apply ℝ ℝ (4 : Fin 5) x

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_restartMixedFlow_two {p : RestartState × ℝ} (hp : restartMixedFlowRegular p) :
    ContDiffAt ℝ 2 restartMixedFlow p := by
  have hc := (contDiffAt_restartMixedChart hp.1 2).comp p contDiffAt_fst
  have hf := (contDiffAt_normalizedMaxCurve_two hp.2.1).comp p (hc.prodMk contDiffAt_snd)
  exact (contDiffAt_restartMixedCoordinates hp.2.2.2.ne' 2).comp p hf

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartMixedFlowRegular_eventually {p : RestartState × ℝ} (hp : restartMixedFlowRegular p) :
    ∀ᶠ q in 𝓝 p, restartMixedFlowRegular q := by
  have hr : ContinuousAt (fun q : RestartState × ℝ => restartRadicand (restartExpCoordinates q.1)) p :=
    ((contDiff_restartRadicand 0).continuous.comp (contDiff_restartExpCoordinates 0).continuous).continuousAt.comp
      continuousAt_fst
  have hc := (contDiffAt_restartMixedChart hp.1 2).comp p contDiffAt_fst
  have he := hc.continuousAt.prodMk continuousAt_snd
  have hf := (contDiffAt_normalizedMaxCurve_two hp.2.1).comp p (hc.prodMk contDiffAt_snd)
  have hpcont := (continuous_apply (0 : Fin 5)).continuousAt.comp hf.continuousAt
  have hncont := (continuous_apply (2 : Fin 5)).continuousAt.comp hf.continuousAt
  filter_upwards [hr.eventually (isOpen_Ioi.mem_nhds hp.1),
    he.eventually ((isOpen_normalizedFlowDomain 0).mem_nhds hp.2.1),
    hpcont.eventually (isOpen_Iio.mem_nhds hp.2.2.1),
    hncont.eventually (isOpen_Ioi.mem_nhds hp.2.2.2)] with q hqr hqd hqp hqn
  exact ⟨hqr, hqd, hqp, hqn⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartMixedFlow_time {y : RestartState} {t : ℝ}
    (H : restartMixedFlowRegular (y, t)) :
    HasDerivAt (fun s => restartMixedFlow (y, s)) (restartMixedField (restartMixedFlow (y, t))) t :=
  hasDerivAt_restartMixedCoordinates (hasDerivAt_normalizedMaxCurve H.2.1)
    ((normalizedMaxCurve_constraint H.2.1).trans (restartMixedChart_constraint H.1.le)) H.2.2.1 H.2.2.2

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartMixedFlow_local_partial_time {p : RestartState × ℝ} (hp : restartMixedFlowRegular p) :
    (fun q => fderiv ℝ restartMixedFlow q (0, 1)) =ᶠ[𝓝 p]
      (fun q => restartMixedField (restartMixedFlow q)) := by
  filter_upwards [restartMixedFlowRegular_eventually hp] with q hq
  have hpath : HasDerivAt (fun s : ℝ => (q.1, s)) (0, 1) q.2 :=
    (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  have HD := ((contDiffAt_restartMixedFlow_two hq).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
    (f := fun s : ℝ => (q.1, s)) q.2 hpath
  exact HD.unique (hasDerivAt_restartMixedFlow_time hq)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartMixedFlow_radicand_pos {p : RestartState × ℝ} (hp : restartMixedFlowRegular p) :
    0 < restartRadicand (restartExpCoordinates (restartMixedFlow p)) := by
  have hc := (normalizedMaxCurve_constraint hp.2.1).trans (restartMixedChart_constraint hp.1.le)
  have H : restartRadicand (restartPhysicalCoordinates (normalizedMaxCurve (restartMixedChart p.1) 0 p.2)) =
      (normalizedMaxCurve (restartMixedChart p.1) 0 p.2 0) ^ 2 := by
    dsimp [stateConstraint, constraint, shearSq] at hc
    dsimp [restartRadicand, restartPhysicalCoordinates]
    linarith only [hc]
  dsimp only [restartMixedFlow]
  rw [restartExpCoordinates_mixed hp.2.2.2, H]
  exact sq_pos_of_neg hp.2.2.1

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartMixedFlow_variation {y : RestartState} {t : ℝ}
    (H : restartMixedFlowRegular (y, t)) (v : RestartState) :
    HasDerivAt (fun s => fderiv ℝ restartMixedFlow (y, s) (v, 0))
      (fderiv ℝ restartMixedField (restartMixedFlow (y, t))
        (fderiv ℝ restartMixedFlow (y, t) (v, 0))) t := by
  have hf : DifferentiableAt ℝ (fun p : ℝ × RestartState => restartMixedField p.2)
      (t, restartMixedFlow (y, t)) :=
    ((contDiffAt_restartMixedField (restartMixedFlow_radicand_pos H) 1).comp
      (t, restartMixedFlow (y, t)) contDiffAt_snd).differentiableAt (by norm_num)
  exact hasDerivAt_parametric_first_variation (contDiffAt_restartMixedFlow_two H) hf
    (restartMixedFlow_local_partial_time H) v

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartMixedFlow_variation_initial {y : RestartState}
    (hy : 0 < restartRadicand (restartExpCoordinates y)) (v : RestartState) :
    fderiv ℝ restartMixedFlow (y, 0) (v, 0) = v := by
  have H : restartMixedFlowRegular (y, 0) := by
    refine ⟨hy, initial_mem_normalizedMaxDomain _ _, ?_, ?_⟩
    · rw [normalizedMaxCurve_initial]
      exact neg_lt_zero.mpr (Real.sqrt_pos.mpr hy)
    · rw [normalizedMaxCurve_initial]
      exact Real.exp_pos _
  rw [← fderiv_parameterSlice_apply ((contDiffAt_restartMixedFlow_two H).differentiableAt (by norm_num)) v]
  simp only [restartMixedFlow_initial, fderiv_fun_id, ContinuousLinearMap.id_apply]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartMixedFlow_fastLayer_regular {C h b T : ℝ} {y : RestartState}
    (hC : 0 ≤ C)
    (hF : ∀ w : RestartState, ‖w‖ ≤ 1 / 16 → ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖)
    (hh : 0 < h ∧ h ≤ 1 / 128) (hb : 0 < b ∧ b ≤ 1 / 16) (hT : 0 ≤ T)
    (hbudget : C * h / 2 + C * b * T ≤ 1 / 4)
    (hn : Real.exp (y 0) ≤ h) (hZ : ‖restartCompactCenterProjection y‖ ≤ b / 2) :
    ∀ t ∈ Icc (0 : ℝ) T, restartMixedFlowRegular (y, t) ∧
      ‖restartExpCoordinates (restartMixedFlow (y, t))‖ ≤ 1 / 16 ∧
      ‖restartExpCoordinates (restartMixedFlow (y, t))‖ ≤ h * Real.exp (-2 * t) + b := by
  have hZsmall : ‖restartCompactCenterProjection y‖ ≤ 1 / 16 := by linarith only [hZ, hb.2]
  have hybox : ‖restartExpCoordinates y‖ ≤ 1 / 16 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16)).mpr
    intro i
    fin_cases i
    · change |Real.exp (y 0)| ≤ 1 / 16
      rw [abs_of_pos (Real.exp_pos _)]
      linarith only [hn, hh.2]
    · exact (norm_le_pi_norm (restartCompactCenterProjection y) 0).trans hZsmall
    · exact (norm_le_pi_norm (restartCompactCenterProjection y) 1).trans hZsmall
    · exact (norm_le_pi_norm (restartCompactCenterProjection y) 2).trans hZsmall
  have hyrad : 0 < restartRadicand (restartExpCoordinates y) := by
    have H := (restartCompact_box_bounds hybox).2.1
    linarith only [H]
  have hc := restartMixedChart_constraint hyrad.le
  have hp : restartMixedChart y 0 < 0 := neg_lt_zero.mpr (Real.sqrt_pos.mpr hyrad)
  have hcenter : restartCenterProjection (restartMixedChart y) = restartCompactCenterProjection y := by
    ext i
    fin_cases i <;> rfl
  have H := normalized_restart_fastLayer_control hC hF hh hb hT hbudget hc hp
    ⟨Real.exp_pos _, hn⟩ (by rwa [hcenter])
  intro t ht
  have Ht := H t ht
  let x := normalizedMaxCurve (restartMixedChart y) 0 t
  have hpos : 0 < x 2 := Ht.1
  have hreg : restartMixedFlowRegular (y, t) :=
    ⟨hyrad, normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1,
      by linarith only [Ht.2.2.1], hpos⟩
  have hnsmall : x 2 ≤ 1 / 16 := by
    have he := Real.exp_le_one_iff.mpr (by linarith only [ht.1] : -2 * t ≤ 0)
    have Hn := Ht.2.1.trans (mul_le_mul_of_nonneg_left he hh.1.le)
    linarith only [Hn, hh.2]
  have hZt : ‖restartCenterProjection x‖ ≤ b := Ht.2.2.2.2.le
  have hexp : restartExpCoordinates (restartMixedFlow (y, t)) = restartPhysicalCoordinates x :=
    restartExpCoordinates_mixed hpos
  refine ⟨hreg, ?_, ?_⟩
  · rw [hexp]
    exact restartPhysicalCoordinates_norm_le (by norm_num)
      (by rwa [abs_of_pos hpos]) (hZt.trans hb.2)
  · rw [hexp]
    have hB : 0 ≤ h * Real.exp (-2 * t) + b :=
      add_nonneg (mul_nonneg hh.1.le (Real.exp_pos _).le) hb.1.le
    apply restartPhysicalCoordinates_norm_le hB
    · rw [abs_of_pos hpos]
      exact Ht.2.1.trans (le_add_of_nonneg_right hb.1.le)
    · exact hZt.trans (le_add_of_nonneg_left (mul_nonneg hh.1.le (Real.exp_pos _).le))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasFDerivAt_restartMixedSection (h : ℝ) (Z : RestartCenterState) :
    HasFDerivAt (restartMixedSection h) restartCenterInclusion Z := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasFDerivAt_const _ _
  · exact hasFDerivAt_apply (𝕜 := ℝ) 0 Z
  · exact hasFDerivAt_apply (𝕜 := ℝ) 1 Z
  · exact hasFDerivAt_apply (𝕜 := ℝ) 2 Z

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartMixedSection_center (h : ℝ) (Z : RestartCenterState) :
    restartCompactCenterProjection (restartMixedSection h Z) = Z := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartMixedChart_section {h : ℝ} (hh : 0 < h) (Z : RestartCenterState) :
    restartMixedChart (restartMixedSection h Z) = restartSectionChart h Z := by
  ext i
  fin_cases i <;> simp [restartMixedChart, restartMixedSection, restartSectionChart,
    restartCompactRoot, restartRadicand, restartExpCoordinates, restartSectionRadicand, Real.exp_log hh]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionMixedFlow_physical {h : ℝ} (hh : 0 < h) (t : ℝ) (Z : RestartCenterState) :
    restartSectionMixedFlow h t Z =
      restartMixedCoordinates (normalizedMaxCurve (restartSectionChart h Z) 0 t) := by
  rw [restartSectionMixedFlow, restartMixedFlow, restartMixedChart_section hh]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionMixedFlow_center {h : ℝ} (hh : 0 < h) (t : ℝ) (Z : RestartCenterState) :
    restartCompactCenterProjection (restartSectionMixedFlow h t Z) = restartSectionCenterFlow h t Z := by
  rw [restartSectionMixedFlow_physical hh]
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionMixedFlow_fderiv_apply {h t : ℝ} {Z : RestartCenterState}
    (H : restartMixedFlowRegular (restartMixedSection h Z, t)) (v : RestartCenterState) :
    fderiv ℝ (restartSectionMixedFlow h t) Z v =
      fderiv ℝ restartMixedFlow (restartMixedSection h Z, t) (restartCenterInclusion v, 0) := by
  have HD := ((contDiffAt_restartMixedFlow_two H).differentiableAt (by norm_num)).hasFDerivAt.comp Z
    ((hasFDerivAt_restartMixedSection h Z).prodMk (hasFDerivAt_const t Z))
  change HasFDerivAt (restartSectionMixedFlow h t) _ Z at HD
  rw [HD.fderiv]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionMixedFlow_fderiv_comparison {C h b T : ℝ} {Z W : RestartCenterState}
    (hC : 0 ≤ C) (hh : 0 ≤ h) (hb : 0 ≤ b)
    (hbudget : C * h / 2 + C * b * T ≤ 1 / 4)
    (HZ : ∀ t ∈ Icc (0 : ℝ) T, restartMixedFlowRegular (restartMixedSection h Z, t))
    (HW : ∀ t ∈ Icc (0 : ℝ) T, restartMixedFlowRegular (restartMixedSection h W, t))
    (HA : ∀ t ∈ Icc (0 : ℝ) T,
      ‖fderiv ℝ restartMixedField (restartSectionMixedFlow h t Z)‖ ≤ C * (h * Real.exp (-2 * t) + b))
    (HJ : ∀ t ∈ Icc (0 : ℝ) T, ‖fderiv ℝ (restartSectionMixedFlow h t) W‖ ≤ 2)
    (HL : ∀ t ∈ Icc (0 : ℝ) T,
      ‖fderiv ℝ restartMixedField (restartSectionMixedFlow h t Z) -
        fderiv ℝ restartMixedField (restartSectionMixedFlow h t W)‖ ≤ 2 * C * ‖Z - W‖) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ‖fderiv ℝ (restartSectionMixedFlow h t) Z - fderiv ℝ (restartSectionMixedFlow h t) W‖ ≤
        8 * C * t * ‖Z - W‖ := by
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  let JZ := fun s => fderiv ℝ restartMixedFlow (restartMixedSection h Z, s) (restartCenterInclusion v, 0)
  let JW := fun s => fderiv ℝ restartMixedFlow (restartMixedSection h W, s) (restartCenterInclusion v, 0)
  let A := fun s => fderiv ℝ restartMixedField (restartSectionMixedFlow h s Z)
  let B := fun s => fderiv ℝ restartMixedField (restartSectionMixedFlow h s W)
  let ε := 4 * C * ‖Z - W‖ * ‖v‖
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have Hder (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun r => JZ r - JW r) (A s (JZ s) - B s (JW s)) s :=
    (hasDerivAt_restartMixedFlow_variation (HZ s hs) (restartCenterInclusion v)).sub
      (hasDerivAt_restartMixedFlow_variation (HW s hs) (restartCenterInclusion v))
  have Hbound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      ‖A s (JZ s) - B s (JW s)‖ ≤
        C * (h * Real.exp (-2 * s) + b) * ‖JZ s - JW s‖ + ε := by
    have heq : A s (JZ s) - B s (JW s) = A s (JZ s - JW s) + (A s - B s) (JW s) := by
      simp only [map_sub, sub_apply]
      abel
    have hJW : ‖JW s‖ ≤ 2 * ‖v‖ := by
      dsimp only [JW]
      rw [← restartSectionMixedFlow_fderiv_apply (HW s hs) v]
      exact ((fderiv ℝ (restartSectionMixedFlow h s) W).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (HJ s hs) (norm_nonneg v))
    rw [heq]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact ((A s).le_opNorm _).trans (mul_le_mul_of_nonneg_right (HA s hs) (norm_nonneg _))
    · apply ((A s - B s).le_opNorm _).trans
      have Hp := mul_le_mul (HL s hs) hJW (norm_nonneg (JW s))
        (by positivity : 0 ≤ 2 * C * ‖Z - W‖)
      dsimp only [ε]
      convert! Hp using 1
      ring
  have Hclock (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      restartFastBudget C h b 0 ≤ restartFastBudget C h b s := by
    rw [restartFastBudget_zero]
    have he := Real.exp_le_one_iff.mpr (by linarith only [hs.1] : -2 * s ≤ 0)
    exact mul_nonneg hC (add_nonneg (mul_nonneg (div_nonneg hh (by norm_num)) (sub_nonneg.mpr he))
      (mul_nonneg hb hs.1))
  have HG := norm_le_exp_of_norm_deriv_clock_forcing Hder
    (fun s _ => hasDerivAt_restartFastBudget C h b s) hε Hclock Hbound t ht
  have Hinit : JZ 0 - JW 0 = 0 := by
    dsimp only [JZ, JW]
    rw [restartMixedFlow_variation_initial (HZ t ht).1,
      restartMixedFlow_variation_initial (HW t ht).1, sub_self]
  rw [Hinit, norm_zero, zero_add, restartFastBudget_zero, sub_zero, sub_zero] at HG
  have HE := (Real.exp_le_exp.mpr ((restartFastBudget_le hC hh hb ht.2).trans hbudget)).trans
    exp_one_quarter_lt_two.le
  have Hfinal := HG.trans (mul_le_mul_of_nonneg_left HE (mul_nonneg hε ht.1))
  change ‖(fderiv ℝ (restartSectionMixedFlow h t) Z - fderiv ℝ (restartSectionMixedFlow h t) W) v‖ ≤ _
  rw [sub_apply, restartSectionMixedFlow_fderiv_apply (HZ t ht),
    restartSectionMixedFlow_fderiv_apply (HW t ht)]
  convert! Hfinal using 1
  dsimp only [ε]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartSectionMixedFlow_fderiv_comparison :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
      ∀ Z W : RestartCenterState, ‖Z‖ ≤ b / 2 → ‖W‖ ≤ b / 2 →
        ∀ t ∈ Icc (0 : ℝ) T,
          ‖fderiv ℝ (restartSectionMixedFlow h t) Z - fderiv ℝ (restartSectionMixedFlow h t) W‖ ≤
            8 * C * t * ‖Z - W‖ := by
  obtain ⟨C₀, hC₀, HC₀⟩ := exists_restartSectionMixedFlow_derivative
  obtain ⟨A, _, HA⟩ := exists_restartCompact_derivative_bounds
  obtain ⟨B, _, HB, HL⟩ := exists_restartMixed_uniform_bounds
  let C := max C₀ (max A B)
  have hC₀C : C₀ ≤ C := le_max_left _ _
  have hC : 32 ≤ C := hC₀.trans hC₀C
  have hC0 : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 32) hC
  have hA : A ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hB : B ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hF (w : RestartState) (hw : ‖w‖ ≤ 1 / 16) : ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖ :=
    (HA w hw).1.trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  refine ⟨C, hC, ?_⟩
  intro h b T hh hCh hb hT hCb Z W hZ hW
  have hhsmall : h ≤ 1 / 128 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.le]
  have hbudget : C * h / 2 + C * b * T ≤ 1 / 4 := by linarith only [hCh, hCb]
  have hsmallh : C₀ * h ≤ 1 / 4 := (mul_le_mul_of_nonneg_right hC₀C hh.le).trans hCh
  have hsmallT : C₀ * b * T ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₀C hb.1.le) hT).trans hCb
  have HD := HC₀ h b T hh hsmallh hb hT hsmallT
  have HR (Y : RestartCenterState) (hY : ‖Y‖ ≤ b / 2) :=
    restartMixedFlow_fastLayer_regular hC0 hF ⟨hh, hhsmall⟩ hb hT hbudget
      (y := restartMixedSection h Y)
      (by change Real.exp (Real.log h) ≤ h; rw [Real.exp_log hh])
      (by rwa [restartMixedSection_center])
  have Hjac (Y : RestartCenterState) (hY : ‖Y‖ ≤ b / 2) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      ‖fderiv ℝ restartMixedField (restartSectionMixedFlow h s Y)‖ ≤ C * (h * Real.exp (-2 * s) + b) :=
    ((HB _ (HR Y hY s hs).2.1).1.trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))).trans
      (mul_le_mul_of_nonneg_left (HR Y hY s hs).2.2 hC0)
  have Hlip (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      ‖fderiv ℝ restartMixedField (restartSectionMixedFlow h s Z) -
        fderiv ℝ restartMixedField (restartSectionMixedFlow h s W)‖ ≤ 2 * C * ‖Z - W‖ := by
    have H1 := (HL _ _ (HR Z hZ s hs).2.1 (HR W hW s hs).2.1).trans
      (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
    have H2 := ((HD s hs).2 Z W hZ hW).trans
      (mul_le_mul_of_nonneg_right exp_one_quarter_lt_two.le (norm_nonneg _))
    have H3 := H1.trans (mul_le_mul_of_nonneg_left H2 hC0)
    convert! H3 using 1
    ring
  exact restartSectionMixedFlow_fderiv_comparison hC0 hh.le hb.1.le hbudget
    (fun s hs => (HR Z hZ s hs).1) (fun s hs => (HR W hW s hs).1)
    (Hjac Z hZ) (fun s hs => ((HD s hs).1 W hW).2.trans exp_one_quarter_lt_two.le) Hlip

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCompactCenterProjection_comp_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : E →L[ℝ] RestartState) :
    ‖restartCompactCenterProjection.comp L‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro v
  exact (restartCompactCenterProjection_norm_le (L v)).trans (L.le_opNorm v)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasFDerivAt_restartSectionCenterFlow_of_mixed {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z) :
    HasFDerivAt (restartSectionCenterFlow h t)
      (restartCompactCenterProjection.comp (fderiv ℝ (restartSectionMixedFlow h t) Z)) Z := by
  have H := restartCompactCenterProjection.hasFDerivAt.comp Z HD.hasFDerivAt
  simpa only [Function.comp_def, restartSectionMixedFlow_center hh] using H

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionCenterFlow_zero {h t : ℝ} (hh : h ^ 2 ≤ 1) (ht : 0 ≤ t) :
    restartSectionCenterFlow h t 0 = 0 := by
  have H := restartReferenceCurve_center_zero h (restartReferenceCurve_forward hh ht).1
  rw [restartSectionCenterFlow, restartSectionChart_zero]
  ext i
  fin_cases i
  · exact H.1
  · exact H.2.1
  · exact H.2.2

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionCenterFlow_fderiv_difference {h t : ℝ} {Z W : RestartCenterState}
    (hh : 0 < h) (HZ : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z)
    (HW : DifferentiableAt ℝ (restartSectionMixedFlow h t) W) :
    ‖fderiv ℝ (restartSectionCenterFlow h t) Z - fderiv ℝ (restartSectionCenterFlow h t) W‖ ≤
      ‖fderiv ℝ (restartSectionMixedFlow h t) Z - fderiv ℝ (restartSectionMixedFlow h t) W‖ := by
  rw [(hasFDerivAt_restartSectionCenterFlow_of_mixed hh HZ).fderiv,
    (hasFDerivAt_restartSectionCenterFlow_of_mixed hh HW).fderiv]
  have heq : restartCompactCenterProjection.comp (fderiv ℝ (restartSectionMixedFlow h t) Z) -
      restartCompactCenterProjection.comp (fderiv ℝ (restartSectionMixedFlow h t) W) =
      restartCompactCenterProjection.comp
        (fderiv ℝ (restartSectionMixedFlow h t) Z - fderiv ℝ (restartSectionMixedFlow h t) W) := by
    ext v i
    simp
  rw [heq]
  exact restartCompactCenterProjection_comp_norm_le _

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartSectionCenterFlow_derivative_comparison :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
      ∀ t ∈ Icc (0 : ℝ) T,
        (∀ Z : RestartCenterState, ‖Z‖ ≤ b / 2 → DifferentiableAt ℝ (restartSectionCenterFlow h t) Z) ∧
        (∀ Z W : RestartCenterState, ‖Z‖ ≤ b / 2 → ‖W‖ ≤ b / 2 →
          ‖fderiv ℝ (restartSectionCenterFlow h t) Z - fderiv ℝ (restartSectionCenterFlow h t) W‖ ≤
            8 * C * t * ‖Z - W‖) := by
  obtain ⟨A, hA, HA⟩ := exists_restartSectionMixedFlow_derivative
  obtain ⟨B, _, HB⟩ := exists_restartSectionMixedFlow_fderiv_comparison
  let C := max A B
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := le_max_right _ _
  refine ⟨C, hA.trans hAC, ?_⟩
  intro h b T hh hCh hb hT hCb t ht
  have HAh : A * h ≤ 1 / 4 := (mul_le_mul_of_nonneg_right hAC hh.le).trans hCh
  have HBh : B * h ≤ 1 / 4 := (mul_le_mul_of_nonneg_right hBC hh.le).trans hCh
  have HAT : A * b * T ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAC hb.1.le) hT).trans hCb
  have HBT : B * b * T ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBC hb.1.le) hT).trans hCb
  have HD := (HA h b T hh HAh hb hT HAT t ht).1
  refine ⟨fun Z hZ => (hasFDerivAt_restartSectionCenterFlow_of_mixed hh (HD Z hZ).1).differentiableAt, ?_⟩
  intro Z W hZ hW
  apply (restartSectionCenterFlow_fderiv_difference hh (HD Z hZ).1 (HD W hW).1).trans
  apply (HB h b T hh HBh hb hT HBT Z W hZ hW t ht).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBC (by norm_num)) ht.1) (norm_nonneg _)

end
end

private theorem BianchiIX.hasFDerivAt_restartSectionRemainder {h t : ℝ} {Z : RestartCenterState}
    (HD : DifferentiableAt ℝ (restartSectionCenterFlow h t) Z) :
    HasFDerivAt (restartSectionRemainder h t)
      (fderiv ℝ (restartSectionCenterFlow h t) Z - restartCenterTransfer h) Z :=
  HD.hasFDerivAt.sub (restartCenterTransfer h).hasFDerivAt

private theorem BianchiIX.restartSectionRemainder_zero {h t : ℝ} (hh : h ^ 2 ≤ 1) (ht : 0 ≤ t) :
    restartSectionRemainder h t 0 = 0 := by
  rw [restartSectionRemainder, restartSectionCenterFlow_zero hh ht, map_zero, sub_self]

private theorem BianchiIX.restartSectionRemainder_bounds {C h b t : ℝ}
    (hh : 0 < h ∧ h ≤ 1 / 16) (ht : 0 ≤ t)
    (HD : ∀ Z : RestartCenterState, ‖Z‖ ≤ b / 2 → DifferentiableAt ℝ (restartSectionCenterFlow h t) Z)
    (HJ : ∀ Z : RestartCenterState, ‖Z‖ ≤ b / 2 →
      ‖fderiv ℝ (restartSectionCenterFlow h t) Z - fderiv ℝ (restartSectionCenterFlow h t) 0‖ ≤
        8 * C * t * ‖Z‖) :
    ∀ Z : RestartCenterState, ‖Z‖ ≤ b / 2 →
      DifferentiableAt ℝ (restartSectionRemainder h t) Z ∧
      ‖restartSectionRemainder h t Z‖ ≤ 4 * C * t * ‖Z‖ ^ 2 + 6 * h * Real.exp (-2 * t) * ‖Z‖ ∧
      ‖fderiv ℝ (restartSectionRemainder h t) Z‖ ≤ 8 * C * t * ‖Z‖ + 6 * h * Real.exp (-2 * t) := by
  have hh2 : h ^ 2 < 1 := by nlinarith only [hh.1, hh.2]
  have Href : fderiv ℝ (restartSectionCenterFlow h t) 0 = restartReferenceCenterDifferential h t :=
    (hasFDerivAt_restartSectionCenterFlow_zero hh2 ht).fderiv
  have Htail := (restartReferenceCenterDifferential_bounds hh ht).2
  have HR (Z : RestartCenterState) (hZ : ‖Z‖ ≤ b / 2) :
      ‖fderiv ℝ (restartSectionRemainder h t) Z‖ ≤ 8 * C * t * ‖Z‖ + 6 * h * Real.exp (-2 * t) := by
    rw [(hasFDerivAt_restartSectionRemainder (HD Z hZ)).fderiv]
    exact (norm_sub_le_norm_sub_add_norm_sub _ (fderiv ℝ (restartSectionCenterFlow h t) 0) _).trans
      (add_le_add (HJ Z hZ) (by simpa only [Href] using Htail))
  intro Z hZ
  have Hθ (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ‖θ • Z‖ ≤ b / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
    exact (mul_le_mul_of_nonneg_right hθ.2 (norm_nonneg Z)).trans (by simpa only [one_mul] using hZ)
  have Hvalue := norm_le_quadratic_of_radial_fderiv
    (restartSectionRemainder_zero hh2.le ht)
    (fun θ hθ => (hasFDerivAt_restartSectionRemainder (HD (θ • Z) (Hθ θ hθ))).differentiableAt)
    (A := 8 * C * t) (B := 6 * h * Real.exp (-2 * t)) (x := Z) (fun θ hθ => by
      have H := HR (θ • Z) (Hθ θ hθ)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1] at H
      convert! H using 1
      ring)
  refine ⟨(hasFDerivAt_restartSectionRemainder (HD Z hZ)).differentiableAt, ?_, HR Z hZ⟩
  convert! Hvalue using 1
  ring

/-- Finite-time nonlinear control uses only the section, initial amplitude, and integrated budget. -/
theorem solution :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ Z : RestartCenterState, ‖Z‖ ≤ b / 2 →
        DifferentiableAt ℝ (restartSectionRemainder h t) Z ∧
        ‖restartSectionRemainder h t Z‖ ≤ 4 * C * t * ‖Z‖ ^ 2 + 6 * h * Real.exp (-2 * t) * ‖Z‖ ∧
        ‖fderiv ℝ (restartSectionRemainder h t) Z‖ ≤ 8 * C * t * ‖Z‖ + 6 * h * Real.exp (-2 * t) := by
  obtain ⟨C, hC, HC⟩ := exists_restartSectionCenterFlow_derivative_comparison
  refine ⟨C, hC, ?_⟩
  intro h b T hh hCh hb hT hCb t ht
  have hhsmall : h ≤ 1 / 16 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.le]
  have H := HC h b T hh hCh hb hT hCb t ht
  apply restartSectionRemainder_bounds ⟨hh, hhsmall⟩ ht.1 H.1
  intro Z hZ
  simpa only [sub_zero] using H.2 Z 0 hZ (by simpa only [norm_zero] using half_pos hb.1 |>.le)
