-- Prove2me | solution 1 for BianchiIX.stableScaledResidualCubic_bounds_of_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T16:24:31.095746+00:00
-- url     : https://prove2.me/submissions/36a964f5-ee83-4c2c-a062-925872993747

import Definitions.Def_BianchiIX_StableProjectionRefinementData
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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
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
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Order.Compact

noncomputable section
open BianchiIX

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
open Filter
open scoped Topology
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem BianchiIX.fderiv2_mul_apply {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => f y * g y)) x v w =
      f x * fderiv ℝ (fderiv ℝ g) x v w +
        fderiv ℝ f x v * fderiv ℝ g x w +
        fderiv ℝ f x w * fderiv ℝ g x v +
        fderiv ℝ (fderiv ℝ f) x v w * g x := by
  have hf' := (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hg' := (hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hp := ((hf.mul hg).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have heq : (fun y => fderiv ℝ (fun z => f z * g z) y w) =ᶠ[𝓝 x]
      (fun y => f y * fderiv ℝ g y w + fderiv ℝ f y w * g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hfy hgy
    rw [fderiv_fun_mul (hfy.differentiableAt (by norm_num)) (hgy.differentiableAt (by norm_num))]
    simp
    ring
  have Hleft := hp.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have Hright := ((hf.differentiableAt (by norm_num)).hasFDerivAt.mul
    (hg'.hasFDerivAt.clm_apply (hasFDerivAt_const w x))).add
    ((hf'.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).mul (hg.differentiableAt (by norm_num)).hasFDerivAt)
  have H := congrArg (fun L : E →L[ℝ] ℝ => L v) (Hleft.unique (Hright.congr_of_eventuallyEq heq))
  simpa [add_assoc, mul_comm, add_comm, add_left_comm] using H

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.fderiv2_finset_sum_apply {ι : Type*} (s : Finset ι) {f : ι → E → F} {x : E}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => ∑ i ∈ s, f i y)) x v w =
      ∑ i ∈ s, fderiv ℝ (fderiv ℝ (f i)) x v w := by
  have heq : fderiv ℝ (fun y => ∑ i ∈ s, f i y) =ᶠ[𝓝 x]
      (fun y => ∑ i ∈ s, fderiv ℝ (f i) y) := by
    have hnear : ∀ᶠ y in 𝓝 x, ∀ i ∈ s, ContDiffAt ℝ 2 (f i) y :=
      (s.eventually_all).mpr (fun i hi => (hf i hi).eventually (by norm_num))
    filter_upwards [hnear] with y hy
    exact fderiv_fun_sum (fun i hi => (hy i hi).differentiableAt (by norm_num))
  have H := HasFDerivAt.fun_sum (u := s) (fun i hi =>
    ((hf i hi).fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num) |>.hasFDerivAt)
  have H' := congrArg (fun L : E →L[ℝ] (E →L[ℝ] F) => L v w) (H.congr_of_eventuallyEq heq).fderiv
  simpa only [sum_apply] using H'

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_stableCubicMonomial (n : WithTop ℕ∞) (i : Fin 4) :
    ContDiff ℝ n (stableCubicMonomial i) := by
  fin_cases i <;> unfold stableCubicMonomial <;> dsimp <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableCubicMonomial {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) (i : Fin 4) :
    HasDerivAt (fun s => stableCubicMonomial i (gamma s)) (stableCubicDifferential i (gamma t) v) t := by
  have hu := hasDerivAt_pi.mp h 1
  have hw := hasDerivAt_pi.mp h 2
  fin_cases i
  · exact hu.pow 3
  · convert! (hu.pow 2).mul hw using 1
    dsimp [stableCubicMonomial, stableCubicDifferential]
    ring
  · convert! hu.mul (hw.pow 2) using 1
    dsimp [stableCubicMonomial, stableCubicDifferential]
    ring
  · exact hw.pow 3

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCubicMonomial_fderiv (i : Fin 4) (y v : StableState) :
    fderiv ℝ (stableCubicMonomial i) y v = stableCubicDifferential i y v := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hd := ((contDiff_stableCubicMonomial 1 i).differentiable (by norm_num) y).hasFDerivAt
  have H := (show HasFDerivAt (stableCubicMonomial i) (fderiv ℝ (stableCubicMonomial i) y)
      (y + (0 : ℝ) • v) by simpa using hd).comp_hasDerivAt 0 hl
  simpa only [zero_smul, add_zero] using H.unique (hasDerivAt_stableCubicMonomial hl i)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableCubicDifferential {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) (i : Fin 4) (w : StableState) :
    HasDerivAt (fun s => stableCubicDifferential i (gamma s) w) (stableCubicHessian i (gamma t) v w) t := by
  have hu := hasDerivAt_pi.mp h 1
  have hw := hasDerivAt_pi.mp h 2
  fin_cases i
  · convert! ((hu.pow 2).const_mul 3).mul_const (w 1) using 1
    dsimp [stableCubicDifferential, stableCubicHessian]
    ring
  · convert! (((hu.const_mul 2).mul hw).mul_const (w 1)).add ((hu.pow 2).mul_const (w 2)) using 1
    dsimp [stableCubicDifferential, stableCubicHessian]
    ring
  · convert! ((hw.pow 2).mul_const (w 1)).add (((hu.const_mul 2).mul hw).mul_const (w 2)) using 1
    dsimp [stableCubicDifferential, stableCubicHessian]
    ring
  · convert! ((hw.pow 2).const_mul 3).mul_const (w 2) using 1
    dsimp [stableCubicDifferential, stableCubicHessian]
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCubicMonomial_fderiv2 (i : Fin 4) (y v w : StableState) :
    fderiv ℝ (fderiv ℝ (stableCubicMonomial i)) y v w = stableCubicHessian i y v w := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hd := ((contDiff_stableCubicMonomial 2 i).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  have H := hasDerivAt_fderiv_apply_const (hd (y + (0 : ℝ) • v)) hl w
  simp only [stableCubicMonomial_fderiv] at H
  simpa only [zero_smul, add_zero] using H.unique (hasDerivAt_stableCubicDifferential hl i w)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCubicMonomial_bound (i : Fin 4) (y : StableState) :
    |stableCubicMonomial i y| ≤ (|y 1| + |y 2|) ^ 3 := by
  let b := |y 1| + |y 2|
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hu : |y 1| ≤ b := by dsimp [b]; linarith [abs_nonneg (y 2)]
  have hw : |y 2| ≤ b := by dsimp [b]; linarith [abs_nonneg (y 1)]
  have hu2 := pow_le_pow_left₀ (abs_nonneg (y 1)) hu 2
  have hw2 := pow_le_pow_left₀ (abs_nonneg (y 2)) hw 2
  fin_cases i
  · exact (abs_pow (y 1) 3).le.trans (pow_le_pow_left₀ (abs_nonneg (y 1)) hu 3)
  · change |y 1 ^ 2 * y 2| ≤ b ^ 3
    rw [abs_mul, abs_pow]
    nlinarith only [mul_le_mul hu2 hw (abs_nonneg _) (sq_nonneg b)]
  · change |y 1 * y 2 ^ 2| ≤ b ^ 3
    rw [abs_mul, abs_pow]
    nlinarith only [mul_le_mul hu hw2 (sq_nonneg _) hb]
  · exact (abs_pow (y 2) 3).le.trans (pow_le_pow_left₀ (abs_nonneg (y 2)) hw 3)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCubicMonomial_first_bound (i : Fin 4) (y v : StableState) :
    |fderiv ℝ (stableCubicMonomial i) y v| ≤ 3 * (|y 1| + |y 2|) ^ 2 * ‖![v 1, v 2]‖ := by
  let b := |y 1| + |y 2|
  let V := ‖![v 1, v 2]‖
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hu : |y 1| ≤ b := by dsimp [b]; linarith [abs_nonneg (y 2)]
  have hw : |y 2| ≤ b := by dsimp [b]; linarith [abs_nonneg (y 1)]
  have hv1 : |v 1| ≤ V := by simpa only [Real.norm_eq_abs, Matrix.cons_val_zero] using norm_le_pi_norm ![v 1, v 2] 0
  have hv2 : |v 2| ≤ V := by simpa only [Real.norm_eq_abs, Matrix.cons_val_one, Matrix.cons_val_zero] using norm_le_pi_norm ![v 1, v 2] 1
  have hp (p q r : ℝ) (hp : |p| ≤ b) (hq : |q| ≤ b) (hr : |r| ≤ V) :
      |p| * |q| * |r| ≤ b ^ 2 * V := by
    have H := mul_le_mul (mul_le_mul hp hq (abs_nonneg _) hb) hr (abs_nonneg _) (mul_nonneg hb hb)
    nlinarith only [H]
  have H11 := hp (y 1) (y 1) (v 1) hu hu hv1
  have H12 := hp (y 1) (y 2) (v 1) hu hw hv1
  have H13 := hp (y 1) (y 1) (v 2) hu hu hv2
  have H21 := hp (y 2) (y 2) (v 1) hw hw hv1
  have H22 := hp (y 1) (y 2) (v 2) hu hw hv2
  have H23 := hp (y 2) (y 2) (v 2) hw hw hv2
  rw [stableCubicMonomial_fderiv]
  fin_cases i
  · change |3 * y 1 ^ 2 * v 1| ≤ _
    simp only [abs_mul, abs_pow]
    norm_num only
    nlinarith only [H11]
  · have H := abs_add_le (2 * y 1 * y 2 * v 1) (y 1 ^ 2 * v 2)
    change |2 * y 1 * y 2 * v 1 + y 1 ^ 2 * v 2| ≤ _
    simp only [abs_mul, abs_pow] at H
    norm_num only at H
    nlinarith only [H, H12, H13]
  · have H := abs_add_le (y 2 ^ 2 * v 1) (2 * y 1 * y 2 * v 2)
    change |y 2 ^ 2 * v 1 + 2 * y 1 * y 2 * v 2| ≤ _
    simp only [abs_mul, abs_pow] at H
    norm_num only at H
    nlinarith only [H, H21, H22]
  · change |3 * y 2 ^ 2 * v 2| ≤ _
    simp only [abs_mul, abs_pow]
    norm_num only
    nlinarith only [H23]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCubicMonomial_second_bound (i : Fin 4) (y v w : StableState) :
    |fderiv ℝ (fderiv ℝ (stableCubicMonomial i)) y v w| ≤
      6 * (|y 1| + |y 2|) * ‖![v 1, v 2]‖ * ‖![w 1, w 2]‖ := by
  let b := |y 1| + |y 2|
  let V := ‖![v 1, v 2]‖
  let W := ‖![w 1, w 2]‖
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hV : 0 ≤ V := norm_nonneg _
  have hu : |y 1| ≤ b := by dsimp [b]; linarith [abs_nonneg (y 2)]
  have hw : |y 2| ≤ b := by dsimp [b]; linarith [abs_nonneg (y 1)]
  have hz (a : StableState) : |a 1| ≤ ‖![a 1, a 2]‖ ∧ |a 2| ≤ ‖![a 1, a 2]‖ := by
    constructor
    · simpa only [Real.norm_eq_abs, Matrix.cons_val_zero] using norm_le_pi_norm ![a 1, a 2] 0
    · simpa only [Real.norm_eq_abs, Matrix.cons_val_one, Matrix.cons_val_zero] using norm_le_pi_norm ![a 1, a 2] 1
  have hp (p q r : ℝ) (hp : |p| ≤ b) (hq : |q| ≤ V) (hr : |r| ≤ W) :
      |p| * |q| * |r| ≤ b * V * W :=
    mul_le_mul (mul_le_mul hp hq (abs_nonneg _) hb) hr (abs_nonneg _) (mul_nonneg hb hV)
  have H111 := hp (y 1) (v 1) (w 1) hu (hz v).1 (hz w).1
  have H211 := hp (y 2) (v 1) (w 1) hw (hz v).1 (hz w).1
  have H112 := hp (y 1) (v 1) (w 2) hu (hz v).1 (hz w).2
  have H121 := hp (y 1) (v 2) (w 1) hu (hz v).2 (hz w).1
  have H212 := hp (y 2) (v 1) (w 2) hw (hz v).1 (hz w).2
  have H221 := hp (y 2) (v 2) (w 1) hw (hz v).2 (hz w).1
  have H122 := hp (y 1) (v 2) (w 2) hu (hz v).2 (hz w).2
  have H222 := hp (y 2) (v 2) (w 2) hw (hz v).2 (hz w).2
  have htri (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
    linarith only [abs_add_le a b, abs_add_le (a + b) c]
  rw [stableCubicMonomial_fderiv2]
  fin_cases i
  · change |6 * y 1 * v 1 * w 1| ≤ _
    simp only [abs_mul]
    norm_num only
    nlinarith only [H111]
  · have H := htri (2 * y 2 * v 1 * w 1) (2 * y 1 * v 1 * w 2) (2 * y 1 * v 2 * w 1)
    change |2 * y 2 * v 1 * w 1 + 2 * y 1 * v 1 * w 2 + 2 * y 1 * v 2 * w 1| ≤ _
    simp only [abs_mul] at H
    norm_num only at H
    nlinarith only [H, H211, H112, H121]
  · have H := htri (2 * y 2 * v 1 * w 2) (2 * y 2 * v 2 * w 1) (2 * y 1 * v 2 * w 2)
    change |2 * y 2 * v 1 * w 2 + 2 * y 2 * v 2 * w 1 + 2 * y 1 * v 2 * w 2| ≤ _
    simp only [abs_mul] at H
    norm_num only at H
    nlinarith only [H, H212, H221, H122]
  · change |6 * y 2 * v 2 * w 2| ≤ _
    simp only [abs_mul]
    norm_num only
    nlinarith only [H222]

end
end

theorem solution {K B : ℝ} {y : StableState} (hB : 0 ≤ B)
    (ha : ∀ i : Fin 4, ContDiffAt ℝ 2 (stableScaledResidualCoefficient K i) y ∧
      |stableScaledResidualCoefficient K i y| ≤ B ∧
      ‖fderiv ℝ (stableScaledResidualCoefficient K i) y‖ ≤ B ∧
      ‖fderiv ℝ (fderiv ℝ (stableScaledResidualCoefficient K i)) y‖ ≤ B) :
    ContDiffAt ℝ 2 (stableScaledResidualCubic K) y ∧
      |stableScaledResidualCubic K y| ≤ 4 * B * (|y 1| + |y 2|) ^ 3 ∧
      (∀ v, |fderiv ℝ (stableScaledResidualCubic K) y v| ≤ 4 * B * stableCubicFirstBudget y v) ∧
      (∀ v w, |fderiv ℝ (fderiv ℝ (stableScaledResidualCubic K)) y v w| ≤ 4 * B * stableCubicSecondBudget y v w) := by
  let f := fun (i : Fin 4) (z : StableState) => stableScaledResidualCoefficient K i z * stableCubicMonomial i z
  have hf (i : Fin 4) : ContDiffAt ℝ 2 (f i) y :=
    (ha i).1.mul (contDiff_stableCubicMonomial 2 i).contDiffAt
  have ha1 (i : Fin 4) (v : StableState) : |fderiv ℝ (stableScaledResidualCoefficient K i) y v| ≤ B * ‖v‖ :=
    ((fderiv ℝ (stableScaledResidualCoefficient K i) y).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (ha i).2.2.1 (norm_nonneg v))
  have ha2 (i : Fin 4) (v w : StableState) : |fderiv ℝ (fderiv ℝ (stableScaledResidualCoefficient K i)) y v w| ≤ B * ‖v‖ * ‖w‖ :=
    (((fderiv ℝ (fderiv ℝ (stableScaledResidualCoefficient K i)) y) v).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ (stableScaledResidualCoefficient K i)) y).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (ha i).2.2.2 (norm_nonneg v))) (norm_nonneg w))
  have h0 (i : Fin 4) : |f i y| ≤ B * (|y 1| + |y 2|) ^ 3 := by
    rw [show f i y = stableScaledResidualCoefficient K i y * stableCubicMonomial i y from rfl, abs_mul]
    exact mul_le_mul (ha i).2.1 (stableCubicMonomial_bound i y) (abs_nonneg _) hB
  have h1 (i : Fin 4) (v : StableState) : |fderiv ℝ (f i) y v| ≤ B * stableCubicFirstBudget y v := by
    dsimp only [f]
    rw [fderiv_fun_mul ((ha i).1.differentiableAt (by norm_num))
      ((contDiff_stableCubicMonomial 1 i).differentiable (by norm_num) y)]
    change |stableScaledResidualCoefficient K i y * fderiv ℝ (stableCubicMonomial i) y v +
      stableCubicMonomial i y * fderiv ℝ (stableScaledResidualCoefficient K i) y v| ≤ _
    have H := abs_add_le (stableScaledResidualCoefficient K i y * fderiv ℝ (stableCubicMonomial i) y v)
      (stableCubicMonomial i y * fderiv ℝ (stableScaledResidualCoefficient K i) y v)
    simp only [abs_mul] at H
    have H0 := mul_le_mul (ha i).2.1 (stableCubicMonomial_first_bound i y v) (abs_nonneg _) hB
    have H1 := mul_le_mul (stableCubicMonomial_bound i y) (ha1 i v) (abs_nonneg _) (by positivity : 0 ≤ (|y 1| + |y 2|) ^ 3)
    dsimp [stableCubicFirstBudget]
    nlinarith only [H, H0, H1]
  have h2 (i : Fin 4) (v w : StableState) : |fderiv ℝ (fderiv ℝ (f i)) y v w| ≤ B * stableCubicSecondBudget y v w := by
    dsimp only [f]
    rw [fderiv2_mul_apply (ha i).1 (contDiff_stableCubicMonomial 2 i).contDiffAt]
    have H0 := mul_le_mul (ha i).2.1 (stableCubicMonomial_second_bound i y v w) (abs_nonneg _) hB
    have H1 := mul_le_mul (ha1 i v) (stableCubicMonomial_first_bound i y w) (abs_nonneg _) (mul_nonneg hB (norm_nonneg v))
    have H2 := mul_le_mul (ha1 i w) (stableCubicMonomial_first_bound i y v) (abs_nonneg _) (mul_nonneg hB (norm_nonneg w))
    have H3 := mul_le_mul (ha2 i v w) (stableCubicMonomial_bound i y) (abs_nonneg _)
      (mul_nonneg (mul_nonneg hB (norm_nonneg v)) (norm_nonneg w))
    have htri (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
      linarith only [abs_add_le a b, abs_add_le (a + b) c, abs_add_le (a + b + c) d]
    have H := htri (stableScaledResidualCoefficient K i y * fderiv ℝ (fderiv ℝ (stableCubicMonomial i)) y v w)
      (fderiv ℝ (stableScaledResidualCoefficient K i) y v * fderiv ℝ (stableCubicMonomial i) y w)
      (fderiv ℝ (stableScaledResidualCoefficient K i) y w * fderiv ℝ (stableCubicMonomial i) y v)
      (fderiv ℝ (fderiv ℝ (stableScaledResidualCoefficient K i)) y v w * stableCubicMonomial i y)
    simp only [abs_mul] at H
    dsimp [stableCubicSecondBudget]
    nlinarith only [H, H0, H1, H2, H3]
  refine ⟨ContDiffAt.sum (fun i _ => hf i), ?_, ?_, ?_⟩
  · exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun i _ => h0 i)).trans_eq (by simp; ring))
  · intro v
    change |fderiv ℝ (fun z => ∑ i : Fin 4, f i z) y v| ≤ _
    rw [fderiv_fun_sum (fun i _ => (hf i).differentiableAt (by norm_num))]
    simp only [sum_apply]
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun i _ => h1 i v)).trans_eq (by simp; ring))
  · intro v w
    change |fderiv ℝ (fderiv ℝ (fun z => ∑ i : Fin 4, f i z)) y v w| ≤ _
    rw [fderiv2_finset_sum_apply Finset.univ (fun i _ => hf i)]
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun i _ => h2 i v w)).trans_eq (by simp; ring))
