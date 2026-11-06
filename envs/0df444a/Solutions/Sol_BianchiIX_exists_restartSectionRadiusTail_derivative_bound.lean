-- Prove2me | solution 1 for BianchiIX.exists_restartSectionRadiusTail_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:42:47.082523+00:00
-- url     : https://prove2.me/submissions/64e36d56-9328-468f-ad84-96f962f066d1

import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_exists_bounds_of_vanishing_axis
import Theorems.Thm_BianchiIX_exists_restartSectionMixedFlow_derivative
import Theorems.Thm_BianchiIX_hasDerivAt_normalized_components
import Theorems.Thm_BianchiIX_le_exp_of_clock_deriv_le
import Theorems.Thm_BianchiIX_norm_le_exp_of_norm_deriv_clock
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_wall_sign
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
import Mathlib.Tactic.Positivity

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.abs_sqrt_sub_sqrt_le_of_relative_error {a b A : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (H : |a - b| ≤ A * b) : |Real.sqrt a - Real.sqrt b| ≤ A * Real.sqrt b := by
  by_cases hb0 : b = 0
  · have Ha : a ≤ 0 := by simpa [hb0, abs_of_nonneg ha] using H
    have ha0 : a = 0 := le_antisymm Ha ha
    simp [ha0, hb0]
  have hbpos : 0 < Real.sqrt b := Real.sqrt_pos.mpr (lt_of_le_of_ne hb (Ne.symm hb0))
  have heq : |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) = |a - b| := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)), ← abs_mul]
    congr 1
    nlinarith only [Real.sq_sqrt ha, Real.sq_sqrt hb]
  have HB : |Real.sqrt a - Real.sqrt b| * Real.sqrt b ≤ (A * Real.sqrt b) * Real.sqrt b := by
    calc
      _ ≤ |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.sqrt_nonneg a)) (abs_nonneg _)
      _ ≤ A * b := heq.le.trans H
      _ = A * (Real.sqrt b) ^ 2 := congrArg (fun x => A * x) (Real.sq_sqrt hb).symm
      _ = _ := by ring
  exact (mul_le_mul_iff_of_pos_right hbpos).mp HB

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

private theorem BianchiIX.restart_coefficients_zero :
    restartShearFactor 0 = 1 ∧ restartWallFactor 0 = 1 ∧ restartShearCoupling 0 = 0 := by
  norm_num [restartShearFactor, restartWallFactor, restartShearCoupling, restartReferenceRoot]

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
open Set

private theorem BianchiIX.exists_fderiv_bound_of_stationary_axis
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : ℝ × E → V} {R : ℝ}
    (hreg : ∀ x : ℝ × E, ‖x‖ ≤ R → ContDiffAt ℝ 3 F x)
    (haxis : ∀ n : ℝ, |n| ≤ R → fderiv ℝ F (n, 0) = 0) :
    ∃ C ≥ (1 : ℝ), ∀ x : ℝ × E, ‖x‖ ≤ R → ‖fderiv ℝ F x‖ ≤ C * ‖x.2‖ := by
  let S := Metric.closedBall (0 : ℝ × E) R
  have hregS (x : ℝ × E) (hx : x ∈ S) := hreg x (by simpa [S] using hx)
  have hc : ContinuousOn (fun x => ‖fderiv ℝ (fderiv ℝ F) x‖) S := by
    intro x hx
    exact (((hregS x hx).fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).continuousAt.norm.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℝ × E) R).exists_bound_of_continuousOn hc
  let C := max B 1
  have hb (x : ℝ × E) (hx : x ∈ S) : ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ C :=
    (le_abs_self _).trans ((hB x hx).trans (le_max_left _ _))
  have hD (x : ℝ × E) (hx : x ∈ S) : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((hregS x hx).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  refine ⟨C, le_max_right _ _, ?_⟩
  intro x hx
  have hn : |x.1| ≤ R := (norm_fst_le x).trans hx
  have hax : (x.1, (0 : E)) ∈ S := by
    simpa [S, Prod.norm_def] using hn
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le hD hb
    (convex_closedBall (0 : ℝ × E) R) hax (by simpa [S] using hx)
  simpa [haxis x.1 hn, Prod.norm_def] using H

end
end

section
noncomputable section
open BianchiIX
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem BianchiIX.norm_fderiv_sqrt_sub_sqrt_le {Q S : E → ℝ} {x : E}
    (HQ : DifferentiableAt ℝ Q x) (HS : DifferentiableAt ℝ S x)
    (hQ : 0 < Q x) (hS : 0 < S x) :
    ‖fderiv ℝ (fun y => Real.sqrt (Q y) - Real.sqrt (S y)) x‖ ≤
      ‖fderiv ℝ (fun y => Q y - S y) x‖ / (2 * Real.sqrt (S x)) +
        |Real.sqrt (Q x) - Real.sqrt (S x)| * ‖fderiv ℝ Q x‖ /
          (2 * Real.sqrt (Q x) * Real.sqrt (S x)) := by
  have hR := Real.sqrt_pos.mpr hQ
  have hP := Real.sqrt_pos.mpr hS
  have HR := HQ.hasFDerivAt.sqrt hQ.ne'
  have HP := HS.hasFDerivAt.sqrt hS.ne'
  have Hdiff := HR.sub HP
  have HD := HQ.hasFDerivAt.sub HS.hasFDerivAt
  change HasFDerivAt (fun y => Real.sqrt (Q y) - Real.sqrt (S y)) _ x at Hdiff
  change HasFDerivAt (fun y => Q y - S y) _ x at HD
  have Heq : fderiv ℝ (fun y => Real.sqrt (Q y) - Real.sqrt (S y)) x =
      (1 / (2 * Real.sqrt (S x))) • fderiv ℝ (fun y => Q y - S y) x +
        ((Real.sqrt (S x) - Real.sqrt (Q x)) / (2 * Real.sqrt (Q x) * Real.sqrt (S x))) • fderiv ℝ Q x := by
    rw [Hdiff.fderiv, HD.fderiv]
    ext v
    simp only [sub_apply, smul_apply, add_apply, smul_eq_mul]
    field_simp
    ring
  rw [Heq]
  apply (norm_add_le _ _).trans_eq
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.sqrt (S x))), abs_div,
    abs_of_pos (by positivity : 0 < 2 * Real.sqrt (Q x) * Real.sqrt (S x)), abs_sub_comm]
  ring

end
end

section
noncomputable section
open BianchiIX
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem BianchiIX.sqrt_sub_sqrt_derivative_bound {Q S : E → ℝ} {x : E} {A c b n : ℝ}
    (HQ : DifferentiableAt ℝ Q x) (HS : DifferentiableAt ℝ S x)
    (hA : 0 ≤ A) (hc : 0 < c) (hb : 0 < b) (hn : 0 ≤ n)
    (hQ : c * b ≤ Real.sqrt (Q x)) (hS : c * b ≤ Real.sqrt (S x))
    (Hval : |Real.sqrt (Q x) - Real.sqrt (S x)| ≤ A * n * b)
    (HDQ : ‖fderiv ℝ Q x‖ ≤ A * b)
    (HDS : ‖fderiv ℝ (fun y => Q y - S y) x‖ ≤ A * n * b) :
    DifferentiableAt ℝ (fun y => Real.sqrt (Q y) - Real.sqrt (S y)) x ∧
      ‖fderiv ℝ (fun y => Real.sqrt (Q y) - Real.sqrt (S y)) x‖ ≤
        (A / c + A ^ 2 / c ^ 2) * n := by
  have hR : 0 < Real.sqrt (Q x) := (mul_pos hc hb).trans_le hQ
  have hP : 0 < Real.sqrt (S x) := (mul_pos hc hb).trans_le hS
  have hQpos := Real.sqrt_pos.mp hR
  have hSpos := Real.sqrt_pos.mp hP
  refine ⟨(HQ.sqrt hQpos.ne').sub (HS.sqrt hSpos.ne'), ?_⟩
  apply (norm_fderiv_sqrt_sub_sqrt_le HQ HS hQpos hSpos).trans
  have Hfirst : ‖fderiv ℝ (fun y => Q y - S y) x‖ / (2 * Real.sqrt (S x)) ≤ A / c * n := by
    calc
      _ ≤ A * n * b / (2 * Real.sqrt (S x)) := div_le_div_of_nonneg_right HDS (by positivity)
      _ ≤ A * n * b / (c * b) := div_le_div_of_nonneg_left (by positivity)
        (mul_pos hc hb) (by linarith only [hS, hP])
      _ = _ := by field_simp
  have Hsecond : |Real.sqrt (Q x) - Real.sqrt (S x)| * ‖fderiv ℝ Q x‖ /
      (2 * Real.sqrt (Q x) * Real.sqrt (S x)) ≤ A ^ 2 / c ^ 2 * n := by
    calc
      _ ≤ (A * n * b) * (A * b) / (2 * Real.sqrt (Q x) * Real.sqrt (S x)) := by
        gcongr
      _ ≤ (A * n * b) * (A * b) / (c * b) ^ 2 := div_le_div_of_nonneg_left (by positivity)
        (sq_pos_of_pos (mul_pos hc hb)) (by
          have HM := mul_le_mul hQ hS (mul_pos hc hb).le hR.le
          nlinarith only [HM, mul_pos hR hP])
      _ = _ := by field_simp
  nlinarith only [Hfirst, Hsecond]

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

private theorem BianchiIX.abs_quadraticFromCoefficients_le (m : Fin 3 → ℝ) (s v : ℝ) :
    |quadraticFromCoefficients m s v| ≤ 2 * ‖m‖ * (s ^ 2 + v ^ 2) := by
  have hm (i : Fin 3) : |m i| ≤ ‖m‖ := norm_le_pi_norm m i
  have hsv : |s| * |v| ≤ s ^ 2 + v ^ 2 := by
    nlinarith only [sq_nonneg (|s| - |v|), sq_abs s, sq_abs v, sq_nonneg s, sq_nonneg v]
  calc
    _ ≤ |m 0 * s ^ 2| + |m 1 * s * v| + |m 2 * v ^ 2| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ‖m‖ * s ^ 2 + ‖m‖ * (|s| * |v|) + ‖m‖ * v ^ 2 := by
      simp only [abs_mul, abs_sq, mul_assoc]
      gcongr
      · exact hm 0
      · exact hm 1
      · exact hm 2
    _ ≤ 2 * ‖m‖ * (s ^ 2 + v ^ 2) := by
      nlinarith only [mul_le_mul_of_nonneg_left hsv (norm_nonneg m)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.abs_quadraticFromCoefficients_le_radius {r s v : ℝ} (m : Fin 3 → ℝ)
    (_hr : 0 ≤ r) (hs : |s| ≤ r) (hv : |v| ≤ 2 * r) :
    |quadraticFromCoefficients m s v| ≤ 12 * ‖m‖ * r ^ 2 := by
  have hs2 : s ^ 2 ≤ r ^ 2 := by
    have H := mul_self_le_mul_self (abs_nonneg s) hs
    nlinarith only [H, sq_abs s]
  have hv2 : v ^ 2 ≤ 4 * r ^ 2 := by
    have H := mul_self_le_mul_self (abs_nonneg v) hv
    nlinarith only [H, sq_abs v]
  exact (abs_quadraticFromCoefficients_le m s v).trans (by
    nlinarith only [mul_le_mul_of_nonneg_left (add_le_add hs2 hv2) (norm_nonneg m),
      mul_nonneg (norm_nonneg m) (sq_nonneg r)])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.abs_quadratic_tangent_le {r d s v ds dv : ℝ} (m dm : Fin 3 → ℝ)
    (hr : 0 ≤ r) (hd : 0 ≤ d) (hs : |s| ≤ r) (hv : |v| ≤ 2 * r)
    (hds : |ds| ≤ d) (hdv : |dv| ≤ 2 * d) :
    |quadraticFromCoefficients dm s v + (2 * m 0 * s + m 1 * v) * ds +
      (m 1 * s + 2 * m 2 * v) * dv| ≤ 12 * ‖dm‖ * r ^ 2 + 24 * ‖m‖ * r * d := by
  have hm (i : Fin 3) : |m i| ≤ ‖m‖ := norm_le_pi_norm m i
  have Hs : |(2 * m 0 * s + m 1 * v) * ds| ≤ 4 * ‖m‖ * r * d := by
    calc
      _ ≤ (|2 * m 0 * s| + |m 1 * v|) * |ds| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (abs_nonneg _)
      _ ≤ (2 * ‖m‖ * r + ‖m‖ * (2 * r)) * d := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        gcongr
        · exact hm 0
        · exact hm 1
      _ = _ := by ring
  have Hv : |(m 1 * s + 2 * m 2 * v) * dv| ≤ 10 * ‖m‖ * r * d := by
    calc
      _ ≤ (|m 1 * s| + |2 * m 2 * v|) * |dv| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (abs_nonneg _)
      _ ≤ (‖m‖ * r + 2 * ‖m‖ * (2 * r)) * (2 * d) := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        gcongr
        · exact hm 1
        · exact hm 2
      _ = _ := by ring
  have H : |quadraticFromCoefficients dm s v + (2 * m 0 * s + m 1 * v) * ds +
      (m 1 * s + 2 * m 2 * v) * dv| ≤ |quadraticFromCoefficients dm s v| +
        |(2 * m 0 * s + m 1 * v) * ds| + |(m 1 * s + 2 * m 2 * v) * dv| :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have HQ := abs_quadraticFromCoefficients_le_radius dm hr hs hv
  nlinarith only [H, HQ, Hs, Hv, mul_nonneg (mul_nonneg (norm_nonneg m) hr) hd]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartQuadratic_coercive {n : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16) (s v : ℝ) :
    s ^ 2 + v ^ 2 ≤ 2 * restartQuadratic n s v := by
  obtain ⟨ha0, _, hc0, _, hk0, hk1⟩ := restart_coefficients_small hn
  have ha2 : 1 ≤ restartShearFactor n ^ 2 := by nlinarith only [ha0]
  have hc2 : 1 ≤ restartWallFactor n ^ 2 := by nlinarith only [hc0]
  have hk2 : 2 * restartShearCoupling n ^ 2 ≤ 1 := by nlinarith only [hk0, hk1, hn.2]
  have HA := mul_le_mul_of_nonneg_right ha2 (sq_nonneg s)
  have HC := mul_le_mul_of_nonneg_right hc2 (sq_nonneg v)
  have HK := mul_le_mul_of_nonneg_right hk2 (sq_nonneg v)
  dsimp only [restartQuadratic]
  nlinarith only [HA, HC, HK, sq_nonneg (restartShearFactor n * s + 2 * restartShearCoupling n * v)]

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

private theorem BianchiIX.restartQuadratic_relative_error {n : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16) (s v : ℝ) :
    |restartQuadratic n s v - (s ^ 2 + v ^ 2)| ≤ 8 * n * (s ^ 2 + v ^ 2) := by
  obtain ⟨ha0, ha1, hc0, hc1, hk0, hk1⟩ := restart_coefficients_small hn
  have hn2 : n ^ 2 ≤ n := by nlinarith only [hn.1, hn.2]
  have haSq := mul_self_le_mul_self (by linarith only [ha0] : 0 ≤ restartShearFactor n)
    (by linarith only [ha1] : restartShearFactor n ≤ 1 + n)
  have hcSq := mul_self_le_mul_self (by linarith only [hc0] : 0 ≤ restartWallFactor n)
    (by linarith only [hc1] : restartWallFactor n ≤ 1 + n)
  have hkSq := mul_self_le_mul_self hk0 hk1
  have hak := mul_le_mul ha1 hk1 hk0 hn.1
  let m : Fin 3 → ℝ := ![restartShearFactor n ^ 2 - 1,
    2 * restartShearFactor n * restartShearCoupling n,
    restartShearCoupling n ^ 2 + restartWallFactor n ^ 2 - 1]
  have hm : ‖m‖ ≤ 4 * n := by
    apply (pi_norm_le_iff_of_nonneg (by positivity [hn.1] : 0 ≤ 4 * n)).mpr
    intro i
    fin_cases i <;> apply abs_le.mpr <;> constructor
    · change -(4 * n) ≤ restartShearFactor n ^ 2 - 1
      nlinarith only [ha0, hn.1]
    · change restartShearFactor n ^ 2 - 1 ≤ 4 * n
      nlinarith only [haSq, hn2, hn.1]
    · change -(4 * n) ≤ 2 * restartShearFactor n * restartShearCoupling n
      nlinarith only [mul_nonneg (by linarith only [ha0] : 0 ≤ restartShearFactor n) hk0, hn.1]
    · change 2 * restartShearFactor n * restartShearCoupling n ≤ 4 * n
      nlinarith only [hak, hk1, hn2]
    · change -(4 * n) ≤ restartShearCoupling n ^ 2 + restartWallFactor n ^ 2 - 1
      nlinarith only [hc0, sq_nonneg (restartShearCoupling n), hn.1]
    · change restartShearCoupling n ^ 2 + restartWallFactor n ^ 2 - 1 ≤ 4 * n
      nlinarith only [hcSq, hkSq, hn2]
  have heq : restartQuadratic n s v - (s ^ 2 + v ^ 2) = quadraticFromCoefficients m s v := by
    dsimp [restartQuadratic, quadraticFromCoefficients, m]
    ring
  rw [heq]
  exact (abs_quadraticFromCoefficients_le m s v).trans (by
    nlinarith only [mul_le_mul_of_nonneg_right hm (add_nonneg (sq_nonneg s) (sq_nonneg v))])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartQuadratic_upper {n : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16) (s v : ℝ) :
    restartQuadratic n s v ≤ 2 * (s ^ 2 + v ^ 2) := by
  have H := (le_abs_self _).trans (restartQuadratic_relative_error hn s v)
  have Hn := mul_le_mul_of_nonneg_right hn.2 (add_nonneg (sq_nonneg s) (sq_nonneg v))
  nlinarith only [H, Hn, sq_nonneg s, sq_nonneg v]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.sqrt_restartQuadratic_tail {n r s v : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16)
    (hr : 0 ≤ r) (hs : |s| ≤ r) (hv : |v| ≤ 2 * r) :
    |Real.sqrt (restartQuadratic n s v) - Real.sqrt (s ^ 2 + v ^ 2)| ≤ 24 * n * r := by
  have HJ : 0 ≤ restartQuadratic n s v := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have HY : 0 ≤ s ^ 2 + v ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have H := abs_sqrt_sub_sqrt_le_of_relative_error HJ HY (restartQuadratic_relative_error hn s v)
  have hs2 := mul_self_le_mul_self (abs_nonneg s) hs
  have hv2 := mul_self_le_mul_self (abs_nonneg v) hv
  have Hnorm : Real.sqrt (s ^ 2 + v ^ 2) ≤ 3 * r := by
    nlinarith only [Real.sq_sqrt HY, Real.sqrt_nonneg (s ^ 2 + v ^ 2), hs2, hv2, sq_abs s, sq_abs v, hr]
  exact H.trans (by nlinarith only [mul_le_mul_of_nonneg_left Hnorm hn.1])

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

private theorem BianchiIX.scalar_clock_comparison {f f' z z' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hb : ∀ t ∈ Icc a b, |f' t| ≤ z' t * f t) :
    ∀ t ∈ Icc a b,
      f a * Real.exp (-(z t - z a)) ≤ f t ∧ f t ≤ f a * Real.exp (z t - z a) := by
  intro t ht
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have HU := le_exp_of_clock_deriv_le (convex_Icc a b) hf hz (c := 1)
    (fun s hs => by simpa only [one_mul] using (le_abs_self _).trans (hb s hs)) ha ht ht.1
  have HL := le_exp_of_clock_deriv_le (convex_Icc a b) (fun s hs => (hf s hs).neg) hz (c := -1)
    (fun s hs => by
      change -f' s ≤ -1 * z' s * (-f s)
      nlinarith only [neg_le_abs (f' s), hb s hs]) ha ht ht.1
  simp only [one_mul] at HU
  simp only [Pi.neg_apply, neg_one_mul] at HL
  exact ⟨by linarith only [HL], HU⟩

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
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_restartSectionStrongWall {h t : ℝ} {Z : RestartCenterState}
    (hZ : 0 < restartSectionRadicand h Z)
    (ht : t ∈ normalizedMaxDomain (restartSectionChart h Z) 0) :
    ContDiffAt ℝ 2 (restartSectionStrongWall h t) Z := by
  have H : ContDiffAt ℝ 2
      (fun W => normalizedMaxCurve (restartSectionChart h W) 0 t) Z :=
    (contDiffAt_normalizedMaxCurve_two ht).comp Z
      (g := fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 0 z.2)
      ((contDiffAt_restartSectionChart hZ 2).prodMk (contDiffAt_const (c := t)))
  exact (contDiffAt_apply ℝ ℝ (2 : Fin 5) _).comp Z H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionStrongWall_pos {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (hZ : 0 ≤ restartSectionRadicand h Z) (ht : 0 ≤ t) :
    0 < restartSectionStrongWall h t Z := by
  have H := normalizedMaxCurve_wall_sign (restartSectionChart_constraint hZ) ht (0 : Fin 3)
  change (restartSectionStrongWall h t Z = 0 ↔ h = 0) ∧
    (0 ≤ restartSectionStrongWall h t Z ↔ 0 ≤ h) at H
  have hne : restartSectionStrongWall h t Z ≠ 0 := fun he => hh.ne' (H.1.mp he)
  exact lt_of_le_of_ne (H.2.mpr hh.le) hne.symm

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionStrongLog_eq {h : ℝ} (hh : 0 < h) (t : ℝ) (Z : RestartCenterState) :
    restartSectionStrongLog h t Z = restartSectionMixedFlow h t Z 0 := by
  rw [restartSectionMixedFlow_physical hh]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_restartSectionStrongLog {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z) :
    HasFDerivAt (restartSectionStrongLog h t)
      ((ContinuousLinearMap.proj (0 : Fin 4)).comp (fderiv ℝ (restartSectionMixedFlow h t) Z)) Z := by
  have H := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) (restartSectionMixedFlow h t Z)).comp Z HD.hasFDerivAt
  convert! H using 1
  ext W
  exact restartSectionStrongLog_eq hh t W

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionStrongLog_fderiv_norm_le {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z) :
    ‖fderiv ℝ (restartSectionStrongLog h t) Z‖ ≤ ‖fderiv ℝ (restartSectionMixedFlow h t) Z‖ := by
  rw [(hasFDerivAt_restartSectionStrongLog hh HD).fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  exact (norm_le_pi_norm (fderiv ℝ (restartSectionMixedFlow h t) Z v) 0).trans
    ((fderiv ℝ (restartSectionMixedFlow h t) Z).le_opNorm v)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_restartSectionStrongWall {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (hZ : 0 < restartSectionRadicand h Z) (ht : 0 ≤ t)
    (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z) :
    HasFDerivAt (restartSectionStrongWall h t)
      (restartSectionStrongWall h t Z • fderiv ℝ (restartSectionStrongLog h t) Z) Z := by
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hZ.le) 0 ht
  have hn := restartSectionStrongWall_pos hh hZ.le ht
  have Hlog := (hasFDerivAt_restartSectionStrongLog hh HD).differentiableAt.hasFDerivAt
  have HE := Hlog.exp
  have heq : (fun W => Real.exp (restartSectionStrongLog h t W)) =ᶠ[𝓝 Z] restartSectionStrongWall h t := by
    filter_upwards [(contDiffAt_restartSectionStrongWall hZ hdom).continuousAt.eventually
      (isOpen_Ioi.mem_nhds hn)] with W hW
    exact Real.exp_log hW
  have H := HE.congr_of_eventuallyEq heq.symm
  simpa only [restartSectionStrongLog, Real.exp_log hn] using H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionStrongWall_fderiv_norm {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (hZ : 0 < restartSectionRadicand h Z) (ht : 0 ≤ t)
    (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z) :
    ‖fderiv ℝ (restartSectionStrongWall h t) Z‖ =
      restartSectionStrongWall h t Z * ‖fderiv ℝ (restartSectionStrongLog h t) Z‖ := by
  rw [(hasFDerivAt_restartSectionStrongWall hh hZ ht HD).fderiv, norm_smul, Real.norm_eq_abs,
    abs_of_pos (restartSectionStrongWall_pos hh hZ.le ht)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartGramCoefficients {n : ℝ} (hn : n ^ 2 < 1) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartGramCoefficients n ∧
      ContDiffAt ℝ k restartRootCoefficients n ∧ ContDiffAt ℝ k restartRotationCoefficients n := by
  obtain ⟨ha, hc, hk⟩ := contDiffAt_restart_coefficients hn k
  constructor
  · rw [contDiffAt_pi]
    intro i
    fin_cases i <;> dsimp [restartGramCoefficients] <;> fun_prop
  constructor <;> rw [contDiffAt_pi] <;> intro i <;>
    fin_cases i <;> dsimp [restartRootCoefficients, restartRotationCoefficients] <;> fun_prop

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

private theorem BianchiIX.restartRadialDriftCoefficients_axis (n : ℝ) : restartRadialDriftCoefficients (n, 0) = 0 := by
  simp [restartRadialDriftCoefficients, restartRadialCurvatureDifference, restartRadialRootDifference,
    restartSectionRadicand, curvature, restartReferenceRoot]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartRotationCoefficients_zero : restartRotationCoefficients 0 = 0 := by
  ext i
  fin_cases i <;> simp [restartRotationCoefficients, restart_coefficients_zero.1,
    restart_coefficients_zero.2.1, restart_coefficients_zero.2.2]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartRadialDriftCoefficients {p : RestartRadialState}
    (hn : p.1 ^ 2 < 1) (hr : 0 < restartSectionRadicand p.1 p.2) :
    ContDiffAt ℝ 3 restartRadialDriftCoefficients p := by
  have hQ : ContDiff ℝ 3 restartRadialCurvatureDifference := by
    unfold restartRadialCurvatureDifference
    fun_prop
  have hrad : ContDiff ℝ 3 (fun p : RestartRadialState => restartSectionRadicand p.1 p.2) := by
    unfold restartSectionRadicand curvature
    fun_prop
  have hroot : ContDiffAt ℝ 3 (fun p : RestartRadialState => restartReferenceRoot p.1) p :=
    (contDiffAt_const.sub (contDiffAt_fst.pow 2)).sqrt (sub_pos.mpr hn).ne'
  have hdiff : ContDiffAt ℝ 3 restartRadialRootDifference p := (hrad.contDiffAt.sqrt hr.ne').sub hroot
  have hG := (contDiffAt_restartGramCoefficients hn 3).1.comp p contDiffAt_fst
  have hH := (contDiffAt_restartGramCoefficients hn 3).2.1.comp p contDiffAt_fst
  have hR := (contDiffAt_restartGramCoefficients hn 3).2.2.comp p contDiffAt_fst
  have hG' := (((contDiffAt_restartGramCoefficients hn 4).1).derivWithin
    (by norm_num : (3 : WithTop ℕ∞) + 1 ≤ 4)).comp p contDiffAt_fst
  unfold restartRadialDriftCoefficients
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasFDerivAt_restartRadialDifferences_zero :
    HasFDerivAt (𝕜 := ℝ) restartRadialCurvatureDifference 0 0 ∧
      HasFDerivAt (𝕜 := ℝ) restartRadialRootDifference 0 0 := by
  have hn : DifferentiableAt ℝ (fun p : RestartRadialState => p.1) 0 := by fun_prop
  have hp (i : Fin 3) : DifferentiableAt ℝ (fun p : RestartRadialState => p.2 i) 0 := by fun_prop
  have hQ : HasFDerivAt (𝕜 := ℝ) restartRadialCurvatureDifference 0 0 := by
    convert! (((hp 1).hasFDerivAt.sub (hp 2).hasFDerivAt).pow 2).sub
      ((hn.hasFDerivAt.mul ((hp 1).hasFDerivAt.add (hp 2).hasFDerivAt)).const_mul 2) using 1
    · ext p
      dsimp [restartRadialCurvatureDifference]
      ring
    · simp
  have hrad : HasFDerivAt (𝕜 := ℝ)
      (fun p : RestartRadialState => restartSectionRadicand p.1 p.2) 0 0 := by
    have H := (((hp 0).hasFDerivAt.pow 2).const_sub 1).sub ((hn.hasFDerivAt.pow 2).add hQ)
    convert! H using 1
    · ext p
      dsimp [restartSectionRadicand, restartRadialCurvatureDifference, curvature]
      ring
    · simp
  have hroot0 : HasFDerivAt (𝕜 := ℝ) (fun p : RestartRadialState => restartReferenceRoot p.1) 0 0 := by
    convert! ((hn.hasFDerivAt.pow 2).const_sub 1).sqrt (by norm_num : (1 : ℝ) - (0 : ℝ) ^ 2 ≠ 0) using 1
    simp
  refine ⟨hQ, ?_⟩
  convert! (hrad.sqrt (by norm_num [restartSectionRadicand, curvature])).sub hroot0 using 1
  simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartRadialDriftCoefficients_fderiv_zero : fderiv ℝ restartRadialDriftCoefficients 0 = 0 := by
  obtain ⟨hQ, hξ⟩ := hasFDerivAt_restartRadialDifferences_zero
  have hn : HasFDerivAt (fun p : RestartRadialState => p.1) (ContinuousLinearMap.fst ℝ ℝ RestartCenterState) 0 :=
    hasFDerivAt_fst
  have hp (i : Fin 3) : DifferentiableAt ℝ (fun p : RestartRadialState => p.2 i) 0 := by fun_prop
  have hg := contDiffAt_restartGramCoefficients (by norm_num : (0 : ℝ) ^ 2 < 1) 2
  have hG := (hg.1.comp (0 : RestartRadialState) contDiffAt_fst).differentiableAt (by norm_num)
  have hH := (hg.2.1.comp (0 : RestartRadialState) contDiffAt_fst).differentiableAt (by norm_num)
  have hR := (hg.2.2.comp (0 : RestartRadialState) contDiffAt_fst).differentiableAt (by norm_num)
  have hG' := ((hg.1.derivWithin (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).comp
    (0 : RestartRadialState) contDiffAt_fst).differentiableAt (by norm_num)
  have H := (((hn.mul (hQ.sub (hξ.const_mul 2))).smul hG'.hasFDerivAt).add
    ((hQ.const_mul 2).smul hG.hasFDerivAt) |>.add
    ((hξ.const_mul 2).smul hH.hasFDerivAt)).add
    ((((hp 1).hasFDerivAt.add (hp 2).hasFDerivAt).const_mul (2 * Real.sqrt 3)).smul hR.hasFDerivAt)
  have HD : HasFDerivAt (𝕜 := ℝ) restartRadialDriftCoefficients 0 0 := by
    convert! H using 1
    simp [restartRadialCurvatureDifference, restartRadialRootDifference, restartSectionRadicand,
      curvature, restartReferenceRoot, restartRotationCoefficients_zero]
  exact HD.fderiv

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_restartRadialDriftCoefficients_bounds :
    ∃ C ≥ (1 : ℝ), ∀ (n : ℝ) (Z : RestartCenterState), |n| ≤ 1 / 16 → ‖Z‖ ≤ 1 / 16 →
      ‖restartRadialDriftCoefficients (n, Z)‖ ≤ C * (|n| + ‖Z‖) * ‖Z‖ ∧
      ‖fderiv ℝ restartRadialDriftCoefficients (n, Z)‖ ≤ C * (|n| + ‖Z‖) ∧
      ‖fderiv ℝ restartRadialDriftCoefficients (n, Z) (1, 0)‖ ≤ C * ‖Z‖ := by
  have hreg (p : RestartRadialState) (hp : ‖p‖ ≤ 1 / 16) :
      ContDiffAt ℝ 3 restartRadialDriftCoefficients p := by
    have hn : |p.1| ≤ 1 / 16 := (norm_fst_le p).trans hp
    have hZ := (norm_snd_le p).trans hp
    exact contDiffAt_restartRadialDriftCoefficients
      (by obtain ⟨hl, hu⟩ := abs_le.mp hn; nlinarith only [hl, hu])
      (restartSectionRadicand_pos_of_small hn hZ)
  obtain ⟨C, hC, HC⟩ := exists_bounds_of_vanishing_axis (by norm_num : (0 : ℝ) ≤ 1 / 16)
    hreg restartRadialDriftCoefficients_axis restartRadialDriftCoefficients_fderiv_zero
  refine ⟨C, hC, ?_⟩
  intro n Z hn hZ
  have H := HC (n, Z) (by simpa only [Prod.norm_def, Real.norm_eq_abs, max_le_iff] using ⟨hn, hZ⟩)
  have hC0 : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 1) hC
  have hnorm : ‖(n, Z)‖ ≤ |n| + ‖Z‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  exact ⟨H.1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm hC0) (norm_nonneg Z)),
    H.2.1.trans (mul_le_mul_of_nonneg_left hnorm hC0), H.2.2⟩

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

private theorem BianchiIX.contDiffAt_restartRadialDrift {p : RestartRadialState}
    (hn : p.1 ^ 2 < 1) (hr : 0 < restartSectionRadicand p.1 p.2) :
    ContDiffAt ℝ 3 restartRadialDrift p := by
  have HM := contDiffAt_restartRadialDriftCoefficients hn hr
  have hm (i : Fin 3) := contDiffAt_pi.mp HM i
  unfold restartRadialDrift quadraticFromCoefficients
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.fderiv_restartRadialDrift_apply {p : RestartRadialState}
    (hn : p.1 ^ 2 < 1) (hr : 0 < restartSectionRadicand p.1 p.2) (w : RestartRadialState) :
    fderiv ℝ restartRadialDrift p w =
      quadraticFromCoefficients (fderiv ℝ restartRadialDriftCoefficients p w) (p.2 0) (p.2 1 - p.2 2) +
      (2 * restartRadialDriftCoefficients p 0 * p.2 0 +
        restartRadialDriftCoefficients p 1 * (p.2 1 - p.2 2)) * w.2 0 +
      (restartRadialDriftCoefficients p 1 * p.2 0 +
        2 * restartRadialDriftCoefficients p 2 * (p.2 1 - p.2 2)) * (w.2 1 - w.2 2) := by
  have HM := (contDiffAt_restartRadialDriftCoefficients hn hr).differentiableAt (by norm_num)
  have hm (i : Fin 3) := hasFDerivAt_pi'.mp HM.hasFDerivAt i
  have hs := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) p.2).comp p (hasFDerivAt_snd (𝕜 := ℝ))
  have hv := ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) p.2).sub
    (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) p.2)).comp p (hasFDerivAt_snd (𝕜 := ℝ))
  have H := (((hm 0).mul (hs.pow 2)).add (((hm 1).mul hs).mul hv)).add ((hm 2).mul (hv.pow 2))
  change HasFDerivAt restartRadialDrift _ p at H
  rw [H.fderiv]
  simp [quadraticFromCoefficients]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.abs_fderiv_restartRadialDrift_apply_le {p : RestartRadialState}
    (hn : p.1 ^ 2 < 1) (hr : 0 < restartSectionRadicand p.1 p.2) (w : RestartRadialState) :
    |fderiv ℝ restartRadialDrift p w| ≤
      12 * ‖fderiv ℝ restartRadialDriftCoefficients p w‖ * ‖p.2‖ ^ 2 +
        24 * ‖restartRadialDriftCoefficients p‖ * ‖p.2‖ * ‖w.2‖ := by
  rw [fderiv_restartRadialDrift_apply hn hr]
  have hb (Z : RestartCenterState) : |Z 1 - Z 2| ≤ 2 * ‖Z‖ := by
    have H := abs_sub (Z 1) (Z 2)
    have H1 : |Z 1| ≤ ‖Z‖ := norm_le_pi_norm Z 1
    have H2 : |Z 2| ≤ ‖Z‖ := norm_le_pi_norm Z 2
    linarith only [H, H1, H2]
  exact abs_quadratic_tangent_le _ _ (norm_nonneg _) (norm_nonneg _)
    (norm_le_pi_norm p.2 0) (hb _) (norm_le_pi_norm w.2 0) (hb _)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_restartRadialDrift_bounds :
    ∃ C ≥ (1 : ℝ), ∀ (n : ℝ) (Z : RestartCenterState),
      (0 ≤ n ∧ n ≤ 1 / 16) → ‖Z‖ ≤ 1 / 16 →
      ContDiffAt ℝ 3 restartRadialDrift (n, Z) ∧
      |restartRadialDrift (n, Z)| ≤ C * (n * ‖Z‖ + ‖Z‖ ^ 2) * restartQuadratic n (Z 0) (Z 1 - Z 2) ∧
      ‖fderiv ℝ (fun W => restartRadialDrift (n, W)) Z‖ ≤ C * (n * ‖Z‖ ^ 2 + ‖Z‖ ^ 3) ∧
      |deriv (fun m => restartRadialDrift (m, Z)) n| ≤ C * ‖Z‖ ^ 3 := by
  obtain ⟨A, hA, HA⟩ := exists_restartRadialDriftCoefficients_bounds
  have hA0 : 0 ≤ A := le_trans (by norm_num : (0 : ℝ) ≤ 1) hA
  refine ⟨36 * A, by linarith only [hA], ?_⟩
  intro n Z hn hZ
  have hnabs : |n| ≤ 1 / 16 := by rw [abs_of_nonneg hn.1]; exact hn.2
  have hn2 : n ^ 2 < 1 := by nlinarith only [hn.1, hn.2]
  have hrad := restartSectionRadicand_pos_of_small hnabs hZ
  have Hreg := contDiffAt_restartRadialDrift (p := (n, Z)) hn2 hrad
  have HM := HA n Z hnabs hZ
  rw [abs_of_nonneg hn.1] at HM
  have hQ0 : 0 ≤ restartQuadratic n (Z 0) (Z 1 - Z 2) := add_nonneg (sq_nonneg _) (sq_nonneg _)
  refine ⟨Hreg, ?_, ?_, ?_⟩
  · apply (abs_quadraticFromCoefficients_le (restartRadialDriftCoefficients (n, Z)) (Z 0) (Z 1 - Z 2)).trans
    have Hco := restartQuadratic_coercive hn (Z 0) (Z 1 - Z 2)
    calc
      _ ≤ 2 * (A * (n + ‖Z‖) * ‖Z‖) * (2 * restartQuadratic n (Z 0) (Z 1 - Z 2)) := by
        gcongr
        · positivity [hn.1]
        · exact HM.1
      _ ≤ 36 * A * (n * ‖Z‖ + ‖Z‖ ^ 2) * restartQuadratic n (Z 0) (Z 1 - Z 2) := by
        nlinarith only [mul_nonneg
          (mul_nonneg (mul_nonneg hA0 (add_nonneg hn.1 (norm_nonneg Z))) (norm_nonneg Z)) hQ0]
  · have HD := (Hreg.differentiableAt (by norm_num)).hasFDerivAt.comp Z
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) n Z)
    change HasFDerivAt (fun W => restartRadialDrift (n, W)) _ Z at HD
    rw [HD.fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [hn.1])
    intro W
    change |fderiv ℝ restartRadialDrift (n, Z) (0, W)| ≤ _
    have HV : ‖fderiv ℝ restartRadialDriftCoefficients (n, Z) (0, W)‖ ≤ A * (n + ‖Z‖) * ‖W‖ := by
      simpa using ((fderiv ℝ restartRadialDriftCoefficients (n, Z)).le_opNorm (0, W)).trans
        (mul_le_mul_of_nonneg_right HM.2.1 (norm_nonneg (0, W)))
    calc
      _ ≤ 12 * ‖fderiv ℝ restartRadialDriftCoefficients (n, Z) (0, W)‖ * ‖Z‖ ^ 2 +
          24 * ‖restartRadialDriftCoefficients (n, Z)‖ * ‖Z‖ * ‖W‖ :=
        abs_fderiv_restartRadialDrift_apply_le (p := (n, Z)) hn2 hrad (0, W)
      _ ≤ 12 * (A * (n + ‖Z‖) * ‖W‖) * ‖Z‖ ^ 2 +
          24 * (A * (n + ‖Z‖) * ‖Z‖) * ‖Z‖ * ‖W‖ := by
        gcongr
        exact HM.1
      _ = _ := by ring
  · have HD := (Hreg.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt n
      ((hasDerivAt_id' n).prodMk (hasDerivAt_const n Z))
    change HasDerivAt (fun m => restartRadialDrift (m, Z)) _ n at HD
    rw [HD.deriv]
    have H := abs_fderiv_restartRadialDrift_apply_le (p := (n, Z)) hn2 hrad (1, 0)
    change |fderiv ℝ restartRadialDrift (n, Z) (1, 0)| ≤ _ at H
    simp only [norm_zero, mul_zero, add_zero] at H
    calc
      _ ≤ 12 * ‖fderiv ℝ restartRadialDriftCoefficients (n, Z) (1, 0)‖ * ‖Z‖ ^ 2 := H
      _ ≤ 12 * (A * ‖Z‖) * ‖Z‖ ^ 2 := by gcongr; exact HM.2.2
      _ ≤ 36 * A * ‖Z‖ ^ 3 := by nlinarith only [mul_nonneg hA0 (pow_nonneg (norm_nonneg Z) 3)]

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

private theorem BianchiIX.fderiv_restartRadialQuadratic_axis {n : ℝ} (hn : n ^ 2 < 1) :
    fderiv ℝ restartRadialQuadratic (n, 0) = 0 := by
  obtain ⟨ha, hc, hk⟩ := contDiffAt_restart_coefficients hn 1
  have hA := (ha.comp (n, (0 : RestartCenterState)) contDiffAt_fst).differentiableAt (by norm_num)
  have hC := (hc.comp (n, (0 : RestartCenterState)) contDiffAt_fst).differentiableAt (by norm_num)
  have hK := (hk.comp (n, (0 : RestartCenterState)) contDiffAt_fst).differentiableAt (by norm_num)
  have hs : DifferentiableAt ℝ (fun p : RestartRadialState => p.2 0) (n, 0) := by fun_prop
  have hv : DifferentiableAt ℝ (fun p : RestartRadialState => p.2 1 - p.2 2) (n, 0) := by fun_prop
  have H := (((hA.hasFDerivAt.mul hs.hasFDerivAt).add (hK.hasFDerivAt.mul hv.hasFDerivAt)).pow 2).add
    ((hC.hasFDerivAt.mul hv.hasFDerivAt).pow 2)
  change HasFDerivAt restartRadialQuadratic _ (n, 0) at H
  rw [H.fderiv]
  simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_restartRadialQuadratic_fderiv_bound :
    ∃ A ≥ (1 : ℝ), ∀ (n : ℝ) (Z : RestartCenterState), |n| ≤ 1 / 16 → ‖Z‖ ≤ 1 / 16 →
      ‖fderiv ℝ restartRadialQuadratic (n, Z)‖ ≤ A * ‖Z‖ := by
  have hreg (p : RestartRadialState) (hp : ‖p‖ ≤ 1 / 16) :
      ContDiffAt ℝ 3 restartRadialQuadratic p := by
    have hn : |p.1| ≤ 1 / 16 := (norm_fst_le p).trans hp
    obtain ⟨hl, hu⟩ := abs_le.mp hn
    exact contDiffAt_restartRadialQuadratic (by nlinarith only [hl, hu]) 3
  obtain ⟨A, hA, HA⟩ := exists_fderiv_bound_of_stationary_axis hreg
    (fun n hn => fderiv_restartRadialQuadratic_axis (by
      obtain ⟨hl, hu⟩ := abs_le.mp hn
      nlinarith only [hl, hu]))
  refine ⟨A, hA, ?_⟩
  intro n Z hn hZ
  exact HA (n, Z) (by simpa only [Prod.norm_def, Real.norm_eq_abs, max_le_iff] using And.intro hn hZ)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartSectionQuadratic_nonneg (h t : ℝ) (Z : RestartCenterState) :
    0 ≤ restartSectionQuadratic h t Z := add_nonneg (sq_nonneg _) (sq_nonneg _)

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

private theorem BianchiIX.hasDerivAt_restartSectionQuadratic {h t : ℝ} {Z : RestartCenterState}
    (hr : 0 ≤ restartSectionRadicand h Z) (ht : 0 ≤ t)
    (hp : normalizedMaxCurve (restartSectionChart h Z) 0 t 0 < 0)
    (hn : restartSectionStrongWall h t Z ^ 2 < 1) :
    HasDerivAt (fun s => restartSectionQuadratic h s Z) (restartSectionQuadraticRate h t Z) t := by
  have H := normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hr) ht
  exact hasDerivAt_restartQuadratic_drift H.1 H.2.1 hp hn

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartGramDefect_zero : restartGramDefect 0 = 0 := by
  ext i
  fin_cases i <;> simp [restartGramDefect, restartGramCoefficients, restart_coefficients_zero.1,
    restart_coefficients_zero.2.1, restart_coefficients_zero.2.2]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiffAt_restartGramDefect {n : ℝ} (hn : n ^ 2 < 1) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartGramDefect n := (contDiffAt_restartGramCoefficients hn k).1.sub contDiffAt_const

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartGramDefect_bounds :
    ∃ A ≥ (1 : ℝ), ∀ n : ℝ, |n| ≤ 1 / 16 →
      ‖restartGramDefect n‖ ≤ A * |n| ∧ ‖fderiv ℝ restartGramDefect n‖ ≤ A := by
  let S := Metric.closedBall (0 : ℝ) (1 / 16)
  have Hreg (n : ℝ) (hn : n ∈ S) : ContDiffAt ℝ 2 restartGramDefect n := by
    have H : |n| ≤ 1 / 16 := by simpa [S] using hn
    obtain ⟨hl, hu⟩ := abs_le.mp H
    exact contDiffAt_restartGramDefect (by nlinarith only [hl, hu]) 2
  have HC : ContinuousOn (fun n => ‖fderiv ℝ restartGramDefect n‖) S := by
    intro n hn
    exact ((Hreg n hn).fderiv_right (m := 1) (by norm_num)).continuousAt.norm.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℝ) (1 / 16)).exists_bound_of_continuousOn HC
  let A := max B 1
  have Hbound (n : ℝ) (hn : n ∈ S) : ‖fderiv ℝ restartGramDefect n‖ ≤ A :=
    (le_abs_self _).trans ((hB n hn).trans (le_max_left _ _))
  refine ⟨A, le_max_right _ _, ?_⟩
  intro n hn
  have hnS : n ∈ S := by simpa [S] using hn
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x hx => (Hreg x hx).differentiableAt (by norm_num)) Hbound
    (convex_closedBall (0 : ℝ) (1 / 16)) (by simp [S] : (0 : ℝ) ∈ S) hnS
  exact ⟨by simpa [restartGramDefect_zero] using H, Hbound n hnS⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartRadialQuadraticDefect_formula (p : RestartRadialState) :
    restartRadialQuadraticDefect p =
      quadraticFromCoefficients (restartGramDefect p.1) (p.2 0) (p.2 1 - p.2 2) := by
  dsimp [restartRadialQuadraticDefect, restartRadialQuadratic, restartQuadratic,
    quadraticFromCoefficients, restartGramDefect, restartGramCoefficients]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiffAt_restartRadialQuadraticDefect {p : RestartRadialState}
    (hn : p.1 ^ 2 < 1) (k : WithTop ℕ∞) : ContDiffAt ℝ k restartRadialQuadraticDefect p := by
  have HQ := contDiffAt_restartRadialQuadratic hn k
  unfold restartRadialQuadraticDefect
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.fderiv_restartRadialQuadraticDefect_apply {p : RestartRadialState}
    (hn : p.1 ^ 2 < 1) (w : RestartRadialState) :
    fderiv ℝ restartRadialQuadraticDefect p w =
      quadraticFromCoefficients (fderiv ℝ restartGramDefect p.1 w.1) (p.2 0) (p.2 1 - p.2 2) +
      (2 * restartGramDefect p.1 0 * p.2 0 + restartGramDefect p.1 1 * (p.2 1 - p.2 2)) * w.2 0 +
      (restartGramDefect p.1 1 * p.2 0 + 2 * restartGramDefect p.1 2 * (p.2 1 - p.2 2)) * (w.2 1 - w.2 2) := by
  have HM := ((contDiffAt_restartGramDefect hn 1).differentiableAt (by norm_num)).hasFDerivAt.comp p hasFDerivAt_fst
  have hm (i : Fin 3) := hasFDerivAt_pi'.mp HM i
  have hs := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) p.2).comp p (hasFDerivAt_snd (𝕜 := ℝ))
  have hv := ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) p.2).sub
    (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) p.2)).comp p (hasFDerivAt_snd (𝕜 := ℝ))
  have H := (((hm 0).mul (hs.pow 2)).add (((hm 1).mul hs).mul hv)).add ((hm 2).mul (hv.pow 2))
  change HasFDerivAt (fun q : RestartRadialState =>
    quadraticFromCoefficients (restartGramDefect q.1) (q.2 0) (q.2 1 - q.2 2)) _ p at H
  have heq : restartRadialQuadraticDefect = fun q =>
      quadraticFromCoefficients (restartGramDefect q.1) (q.2 0) (q.2 1 - q.2 2) :=
    funext restartRadialQuadraticDefect_formula
  rw [heq, H.fderiv]
  simp [quadraticFromCoefficients]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartRadialQuadraticDefect_tangent_bound :
    ∃ A ≥ (1 : ℝ), ∀ (n : ℝ) (Z : RestartCenterState), |n| ≤ 1 / 16 → ∀ w : RestartRadialState,
      |fderiv ℝ restartRadialQuadraticDefect (n, Z) w| ≤
        12 * A * |w.1| * ‖Z‖ ^ 2 + 24 * A * |n| * ‖Z‖ * ‖w.2‖ := by
  obtain ⟨A, hA, HA⟩ := exists_restartGramDefect_bounds
  refine ⟨A, hA, ?_⟩
  intro n Z hn w
  have hn2 : n ^ 2 < 1 := by obtain ⟨hl, hu⟩ := abs_le.mp hn; nlinarith only [hl, hu]
  have hdiff (V : RestartCenterState) : |V 1 - V 2| ≤ 2 * ‖V‖ := by
    have H1 : |V 1| ≤ ‖V‖ := norm_le_pi_norm V 1
    have H2 : |V 2| ≤ ‖V‖ := norm_le_pi_norm V 2
    linarith only [abs_sub (V 1) (V 2), H1, H2]
  rw [fderiv_restartRadialQuadraticDefect_apply (p := (n, Z)) hn2]
  apply (abs_quadratic_tangent_le _ _ (norm_nonneg Z) (norm_nonneg w.2)
    (norm_le_pi_norm Z 0) (hdiff Z) (norm_le_pi_norm w.2 0) (hdiff w.2)).trans
  have HD : ‖fderiv ℝ restartGramDefect n w.1‖ ≤ A * |w.1| :=
    ((fderiv ℝ restartGramDefect n).le_opNorm w.1).trans
      (mul_le_mul_of_nonneg_right (HA n hn).2 (abs_nonneg _))
  calc
    _ ≤ 12 * (A * |w.1|) * ‖Z‖ ^ 2 + 24 * (A * |n|) * ‖Z‖ * ‖w.2‖ := by
      gcongr
      exact (HA n hn).1
    _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartSectionQuadratic_control :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ) (Z : RestartCenterState),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 → ‖Z‖ ≤ b / 2 →
      ∀ t ∈ Icc (0 : ℝ) T,
        0 < restartSectionStrongWall h t Z ∧ restartSectionStrongWall h t Z ≤ h * Real.exp (-2 * t) ∧
        restartSectionStrongWall h t Z ≤ 1 / 16 ∧ ‖restartSectionCenterFlow h t Z‖ ≤ b ∧
        HasDerivAt (fun s => restartSectionQuadratic h s Z) (restartSectionQuadraticRate h t Z) t ∧
        |restartSectionQuadraticRate h t Z| ≤ C *
          (restartSectionStrongWall h t Z * ‖restartSectionCenterFlow h t Z‖ + ‖restartSectionCenterFlow h t Z‖ ^ 2) *
            restartSectionQuadratic h t Z ∧
        restartSectionQuadratic h 0 Z / 2 ≤ restartSectionQuadratic h t Z ∧
        restartSectionQuadratic h t Z ≤ 2 * restartSectionQuadratic h 0 Z := by
  obtain ⟨A, hA, HA⟩ := exists_restartSection_fastLayer_control
  obtain ⟨B, _, HB⟩ := exists_restartRadialDrift_bounds
  let C := max A B
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := le_max_right _ _
  have hC : 32 ≤ C := hA.trans hAC
  have hC0 : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 32) hC
  refine ⟨C, hC, ?_⟩
  intro h b T Z hh hCh hb hT hCb hZ
  have HAh : A * h ≤ 1 / 4 := (mul_le_mul_of_nonneg_right hAC hh.le).trans hCh
  have HAb : A * b * T ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAC hb.1.le) hT).trans hCb
  have HF := HA h b T Z hh HAh hb hT HAb hZ
  have hhsmall : h ≤ 1 / 128 := by nlinarith only [hC, hCh, hh]
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rw [abs_of_pos hh]; linarith only [hhsmall]) (by linarith only [hZ, hb.2])
  have Hn (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      0 < restartSectionStrongWall h t Z ∧ restartSectionStrongWall h t Z ≤ 1 / 16 := by
    have HE := Real.exp_le_one_iff.mpr (by linarith only [ht.1] : -2 * t ≤ 0)
    exact ⟨(HF t ht).1, (HF t ht).2.1.trans
      ((mul_le_mul_of_nonneg_left HE hh.le).trans (by linarith only [hhsmall]))⟩
  have Hz (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖restartSectionCenterFlow h t Z‖ ≤ b :=
    (HF t ht).2.2.2.2.le
  have HD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun s => restartSectionQuadratic h s Z) (restartSectionQuadraticRate h t Z) t :=
    hasDerivAt_restartSectionQuadratic hrad.le ht.1
      (by linarith only [(HF t ht).2.2.1])
      (by nlinarith only [(Hn t ht).1, (Hn t ht).2])
  have HR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      |restartSectionQuadraticRate h t Z| ≤ C *
        (restartSectionStrongWall h t Z * ‖restartSectionCenterFlow h t Z‖ + ‖restartSectionCenterFlow h t Z‖ ^ 2) *
          restartSectionQuadratic h t Z := by
    have H := (HB _ _ ⟨(Hn t ht).1.le, (Hn t ht).2⟩ ((Hz t ht).trans hb.2)).2.1
    exact H.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hBC (add_nonneg
        (mul_nonneg (Hn t ht).1.le (norm_nonneg _)) (sq_nonneg _)))
      (restartSectionQuadratic_nonneg h t Z))
  have HG (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      |restartSectionQuadraticRate h t Z| ≤ C * (h * Real.exp (-2 * t) + b) * restartSectionQuadratic h t Z := by
    have hr1 : ‖restartSectionCenterFlow h t Z‖ ≤ 1 := (Hz t ht).trans (by linarith only [hb.2])
    have Hcoeff : restartSectionStrongWall h t Z * ‖restartSectionCenterFlow h t Z‖ +
        ‖restartSectionCenterFlow h t Z‖ ^ 2 ≤ h * Real.exp (-2 * t) + b := by
      have Hs : ‖restartSectionCenterFlow h t Z‖ ^ 2 ≤ ‖restartSectionCenterFlow h t Z‖ := by
        nlinarith only [mul_nonneg (norm_nonneg (restartSectionCenterFlow h t Z)) (sub_nonneg.mpr hr1)]
      have Hn' := mul_le_mul_of_nonneg_left hr1 (Hn t ht).1.le
      have HE : restartSectionStrongWall h t Z ≤ h * Real.exp (-2 * t) := (HF t ht).2.1
      nlinarith only [Hs, Hn', HE, Hz t ht]
    exact (HR t ht).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left Hcoeff hC0) (restartSectionQuadratic_nonneg h t Z))
  have Hcomp := scalar_clock_comparison HD (fun t _ => hasDerivAt_restartFastBudget C h b t) HG
  intro t ht
  have HE : restartFastBudget C h b t ≤ 1 / 4 :=
    (restartFastBudget_le hC0 hh.le hb.1.le ht.2).trans (by linarith only [hCh, hCb])
  have Hexp := (Real.exp_le_exp.mpr HE).trans exp_one_quarter_lt_two.le
  have Hinv : 1 / 2 ≤ Real.exp (-restartFastBudget C h b t) := by
    have H := mul_le_mul_of_nonneg_right Hexp (Real.exp_pos (-restartFastBudget C h b t)).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at H
    linarith only [H]
  have HC := Hcomp t ht
  rw [restartFastBudget_zero, sub_zero] at HC
  refine ⟨(Hn t ht).1, (HF t ht).2.1, (Hn t ht).2, Hz t ht, HD t ht, HR t ht, ?_, ?_⟩
  · have H := mul_le_mul_of_nonneg_left Hinv (restartSectionQuadratic_nonneg h 0 Z)
    linarith only [H, HC.1]
  · exact HC.2.trans (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left Hexp (restartSectionQuadratic_nonneg h 0 Z))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartSectionRadialState_derivative {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (hZ : 0 < restartSectionRadicand h Z) (ht : 0 ≤ t)
    (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z)
    (HB : ‖fderiv ℝ (restartSectionMixedFlow h t) Z‖ ≤ 2)
    (hn : restartSectionStrongWall h t Z ≤ 1) :
    DifferentiableAt ℝ (restartSectionRadialState h t) Z ∧
      ‖fderiv ℝ (restartSectionRadialState h t) Z‖ ≤ 2 ∧
      ∀ v : RestartCenterState,
        |(fderiv ℝ (restartSectionRadialState h t) Z v).1| ≤
          2 * restartSectionStrongWall h t Z * ‖v‖ := by
  have Hn := hasFDerivAt_restartSectionStrongWall hh hZ ht HD
  have HZ := hasFDerivAt_restartSectionCenterFlow_of_mixed hh HD
  have HP := Hn.prodMk HZ
  change HasFDerivAt (restartSectionRadialState h t) _ Z at HP
  have hnpos := restartSectionStrongWall_pos hh hZ.le ht
  have Hlog := (restartSectionStrongLog_fderiv_norm_le hh HD).trans HB
  have hnD : ‖fderiv ℝ (restartSectionStrongWall h t) Z‖ ≤ 2 * restartSectionStrongWall h t Z := by
    rw [restartSectionStrongWall_fderiv_norm hh hZ ht HD]
    nlinarith only [mul_le_mul_of_nonneg_left Hlog hnpos.le]
  have hZD : ‖fderiv ℝ (restartSectionCenterFlow h t) Z‖ ≤ 2 := by
    rw [HZ.fderiv]
    exact (restartCompactCenterProjection_comp_norm_le _).trans HB
  have hfst (v : RestartCenterState) :
      |(fderiv ℝ (restartSectionRadialState h t) Z v).1| ≤ 2 * restartSectionStrongWall h t Z * ‖v‖ := by
    rw [HP.fderiv]
    change |(restartSectionStrongWall h t Z • fderiv ℝ (restartSectionStrongLog h t) Z) v| ≤ _
    rw [← Hn.fderiv]
    exact ((fderiv ℝ (restartSectionStrongWall h t) Z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hnD (norm_nonneg _))
  refine ⟨HP.differentiableAt, ?_, hfst⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  rw [Prod.norm_def, max_le_iff]
  constructor
  · exact (hfst v).trans (by nlinarith only [mul_le_mul_of_nonneg_right hn (norm_nonneg v)])
  · rw [HP.fderiv]
    change ‖(restartCompactCenterProjection.comp (fderiv ℝ (restartSectionMixedFlow h t) Z)) v‖ ≤ _
    rw [← HZ.fderiv]
    exact ((fderiv ℝ (restartSectionCenterFlow h t) Z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hZD (norm_nonneg _))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartSectionQuadratic_derivative_bound {h t A b : ℝ} {Z : RestartCenterState}
    (hA : 0 ≤ A) (hb : 0 ≤ b)
    (HD : DifferentiableAt ℝ (restartSectionRadialState h t) Z)
    (HB : ‖fderiv ℝ (restartSectionRadialState h t) Z‖ ≤ 2)
    (hn : restartSectionStrongWall h t Z ^ 2 < 1)
    (HQ : ‖fderiv ℝ restartRadialQuadratic (restartSectionRadialState h t Z)‖ ≤ A * b) :
    DifferentiableAt ℝ (restartSectionQuadratic h t) Z ∧
      ‖fderiv ℝ (restartSectionQuadratic h t) Z‖ ≤ 2 * A * b := by
  have H := ((contDiffAt_restartRadialQuadratic hn 1).differentiableAt (by norm_num)).hasFDerivAt.comp Z HD.hasFDerivAt
  change HasFDerivAt (restartSectionQuadratic h t) _ Z at H
  refine ⟨H.differentiableAt, ?_⟩
  rw [H.fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul HQ HB (norm_nonneg _) (mul_nonneg hA hb)).trans_eq (by ring))

end
end

private theorem BianchiIX.restartSectionQuadraticDefect_derivative_bound {h t A b : ℝ} {Z : RestartCenterState}
    (hA : 0 ≤ A) (hb : 0 ≤ b ∧ b ≤ 1)
    (HD : DifferentiableAt ℝ (restartSectionRadialState h t) Z)
    (HB : ‖fderiv ℝ (restartSectionRadialState h t) Z‖ ≤ 2)
    (Hn : ∀ v : RestartCenterState,
      |(fderiv ℝ (restartSectionRadialState h t) Z v).1| ≤ 2 * restartSectionStrongWall h t Z * ‖v‖)
    (hn : 0 ≤ restartSectionStrongWall h t Z ∧ restartSectionStrongWall h t Z ≤ 1 / 16)
    (hcenter : ‖restartSectionCenterFlow h t Z‖ ≤ b)
    (HF : ∀ w : RestartRadialState,
      |fderiv ℝ restartRadialQuadraticDefect (restartSectionRadialState h t Z) w| ≤
        12 * A * |w.1| * ‖restartSectionCenterFlow h t Z‖ ^ 2 +
          24 * A * |restartSectionStrongWall h t Z| * ‖restartSectionCenterFlow h t Z‖ * ‖w.2‖) :
    ‖fderiv ℝ (fun W => restartRadialQuadraticDefect (restartSectionRadialState h t W)) Z‖ ≤
      72 * A * restartSectionStrongWall h t Z * b := by
  have hn0 := hn.1
  have hb0 := hb.1
  have hn2 : restartSectionStrongWall h t Z ^ 2 < 1 := by nlinarith only [hn.1, hn.2]
  have H := ((contDiffAt_restartRadialQuadraticDefect hn2 1).differentiableAt (by norm_num)).hasFDerivAt.comp Z HD.hasFDerivAt
  change HasFDerivAt (fun W => restartRadialQuadraticDefect (restartSectionRadialState h t W)) _ Z at H
  rw [H.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have HW : ‖(fderiv ℝ (restartSectionRadialState h t) Z v).2‖ ≤ 2 * ‖v‖ :=
    (norm_snd_le _).trans (((fderiv ℝ (restartSectionRadialState h t) Z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right HB (norm_nonneg _)))
  have Hsq : b ^ 2 ≤ b := by nlinarith only [mul_nonneg hb0 (sub_nonneg.mpr hb.2)]
  have Hraw := HF (fderiv ℝ (restartSectionRadialState h t) Z v)
  rw [abs_of_nonneg hn.1] at Hraw
  calc
    _ ≤ 12 * A * |(fderiv ℝ (restartSectionRadialState h t) Z v).1| * ‖restartSectionCenterFlow h t Z‖ ^ 2 +
        24 * A * restartSectionStrongWall h t Z * ‖restartSectionCenterFlow h t Z‖ *
          ‖(fderiv ℝ (restartSectionRadialState h t) Z v).2‖ := Hraw
    _ ≤ 12 * A * (2 * restartSectionStrongWall h t Z * ‖v‖) * b ^ 2 +
        24 * A * restartSectionStrongWall h t Z * b * (2 * ‖v‖) := by
      gcongr
      exact Hn v
    _ ≤ _ := by
      nlinarith only [mul_le_mul_of_nonneg_left Hsq
        (by positivity : 0 ≤ A * restartSectionStrongWall h t Z * ‖v‖)]

/-- The endpoint reference error has an ordinary initial derivative of order the actual strong wall. -/
theorem solution :
    ∃ C ≥ (32 : ℝ), ∀ c : ℝ, 0 < c → ∃ K : ℝ, 0 < K ∧
      ∀ (h b T : ℝ) (Z : RestartCenterState),
        0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
        ‖Z‖ ≤ b / 2 → c * b ≤ restartRadialNorm Z → ∀ t ∈ Icc (0 : ℝ) T,
          DifferentiableAt ℝ (restartSectionRadiusTail h t) Z ∧
          ‖fderiv ℝ (restartSectionRadiusTail h t) Z‖ ≤ K * restartSectionStrongWall h t Z := by
  obtain ⟨A, hA, HA⟩ := exists_restartSectionQuadratic_control
  obtain ⟨B, _, HB⟩ := exists_restartSectionMixedFlow_derivative
  obtain ⟨D, hD, HD⟩ := exists_restartRadialQuadraticDefect_tangent_bound
  obtain ⟨E, _, HE⟩ := exists_restartRadialQuadratic_fderiv_bound
  let C := max A (max B (max D E))
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hDC : D ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hEC : E ≤ C := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hC : 32 ≤ C := hA.trans hAC
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  have hD0 : 0 ≤ D := le_trans (by norm_num : (0 : ℝ) ≤ 1) hD
  refine ⟨C, hC, ?_⟩
  intro c hc
  let K := (72 * C) / (c / 4) + (72 * C) ^ 2 / (c / 4) ^ 2
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro h b T Z hh hCh hb hT hCb hZ hradial t ht
  have hbpos := hb.1
  have hb0 := hb.1.le
  have hsmall : h ≤ 1 / 16 := by nlinarith only [hC, hCh, hh]
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rwa [abs_of_pos hh]) (by linarith only [hZ, hb.2])
  have Hheight (k : ℝ) (hk : k ≤ C) : k * h ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_right hk hh.le).trans hCh
  have Htime (k : ℝ) (hk : k ≤ C) : k * b * T ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk hb0) hT).trans hCb
  have H := HA h b T Z hh (Hheight A hAC) hb hT (Htime A hAC) hZ t ht
  have HM := (HB h b T hh (Hheight B hBC) hb hT (Htime B hBC) t ht).1 Z hZ
  have hn : 0 ≤ restartSectionStrongWall h t Z ∧ restartSectionStrongWall h t Z ≤ 1 / 16 :=
    ⟨H.1.le, H.2.2.1⟩
  have hn0 := hn.1
  have hnabs : |restartSectionStrongWall h t Z| ≤ 1 / 16 := by rw [abs_of_nonneg hn.1]; exact hn.2
  have hn2 : restartSectionStrongWall h t Z ^ 2 < 1 := by nlinarith only [hn.1, hn.2]
  have Hcenter : ‖restartSectionCenterFlow h t Z‖ ≤ b := H.2.2.2.1
  have Hstate := restartSectionRadialState_derivative hh hrad ht.1 HM.1
    (HM.2.trans exp_one_quarter_lt_two.le) (by linarith only [hn.2])
  have HQfield : ‖fderiv ℝ restartRadialQuadratic (restartSectionRadialState h t Z)‖ ≤ C * b :=
    (HE _ _ hnabs (Hcenter.trans hb.2)).trans (mul_le_mul hEC Hcenter (norm_nonneg _) hCpos.le)
  have HQ := restartSectionQuadratic_derivative_bound hCpos.le hb0 Hstate.1 Hstate.2.1 hn2 HQfield
  let S := fun W : RestartCenterState => restartSectionCenterFlow h t W 0 ^ 2 +
    (restartSectionCenterFlow h t W 1 - restartSectionCenterFlow h t W 2) ^ 2
  have HZdiff : DifferentiableAt ℝ (restartSectionCenterFlow h t) Z := Hstate.1.snd
  have HS : DifferentiableAt ℝ S Z := by dsimp only [S]; fun_prop
  have HSnonneg : 0 ≤ S Z := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have HlowerR : c * b / 2 ≤ restartSectionRadius h t Z := by
    have Hraw : restartRadialNorm Z ^ 2 = Z 0 ^ 2 + (Z 1 - Z 2) ^ 2 :=
      Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have Hco := restartQuadratic_coercive ⟨hh.le, hsmall⟩ (Z 0) (Z 1 - Z 2)
    rw [← restartSectionQuadratic_initial h Z] at Hco
    have Hcb := mul_self_le_mul_self (mul_pos hc hb.1).le hradial
    have Hsq : restartSectionRadius h t Z ^ 2 = restartSectionQuadratic h t Z :=
      Real.sq_sqrt (restartSectionQuadratic_nonneg h t Z)
    have HR0 : 0 ≤ restartSectionRadius h t Z := Real.sqrt_nonneg _
    nlinarith only [Hraw, Hco, Hcb, Hsq, HR0, H.2.2.2.2.2.2.1, mul_pos hc hb.1]
  have HlowerS : c / 4 * b ≤ Real.sqrt (S Z) := by
    have Hupper := restartQuadratic_upper hn (restartSectionCenterFlow h t Z 0)
      (restartSectionCenterFlow h t Z 1 - restartSectionCenterFlow h t Z 2)
    change restartSectionQuadratic h t Z ≤ 2 * S Z at Hupper
    have Hsq : restartSectionRadius h t Z ^ 2 = restartSectionQuadratic h t Z :=
      Real.sq_sqrt (restartSectionQuadratic_nonneg h t Z)
    have HR0 : 0 ≤ restartSectionRadius h t Z := Real.sqrt_nonneg _
    have Hcmp : restartSectionRadius h t Z ≤ 2 * Real.sqrt (S Z) := by
      nlinarith only [Hupper, Hsq, Real.sq_sqrt HSnonneg, Real.sqrt_nonneg (S Z), HR0]
    linarith only [Hcmp, HlowerR]
  have Hvalue : |restartSectionRadius h t Z - Real.sqrt (S Z)| ≤ (72 * C) * restartSectionStrongWall h t Z * b := by
    have H1 : |restartSectionCenterFlow h t Z 1| ≤ b := (norm_le_pi_norm _ 1).trans Hcenter
    have H2 : |restartSectionCenterFlow h t Z 2| ≤ b := (norm_le_pi_norm _ 2).trans Hcenter
    have HV := sqrt_restartQuadratic_tail hn hb0 ((norm_le_pi_norm _ 0).trans Hcenter)
      (by linarith only [abs_sub (restartSectionCenterFlow h t Z 1) (restartSectionCenterFlow h t Z 2), H1, H2])
    exact HV.trans (by nlinarith only [mul_le_mul_of_nonneg_right hC (mul_nonneg hn0 hb0), mul_nonneg hn0 hb0])
  have Hdef := restartSectionQuadraticDefect_derivative_bound hD0
    ⟨hb0, by linarith only [hb.2]⟩ Hstate.1 Hstate.2.1 Hstate.2.2 hn Hcenter (HD _ _ hnabs)
  have HDS : ‖fderiv ℝ (fun W => restartSectionQuadratic h t W - S W) Z‖ ≤
      (72 * C) * restartSectionStrongWall h t Z * b := by
    apply Hdef.trans
    gcongr
  have HDQ : ‖fderiv ℝ (restartSectionQuadratic h t) Z‖ ≤ (72 * C) * b :=
    HQ.2.trans (by nlinarith only [mul_nonneg hCpos.le hb0])
  exact sqrt_sub_sqrt_derivative_bound HQ.1 HS (by positivity : 0 ≤ 72 * C)
    (by positivity : 0 < c / 4) hb.1 hn.1
    (by change c / 4 * b ≤ restartSectionRadius h t Z; nlinarith only [HlowerR, mul_pos hc hb.1])
    HlowerS Hvalue HDQ HDS
