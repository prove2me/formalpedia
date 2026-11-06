-- Prove2me | solution 1 for BianchiIX.reciprocalProfile_derivative_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T16:24:12.648784+00:00
-- url     : https://prove2.me/submissions/21ba56a2-fc99-436f-9efd-314f3330c6cd

import Definitions.Def_BianchiIX_StableProjectionRefinementData
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Data.Fin.VecNotation

noncomputable section
open BianchiIX

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

private theorem BianchiIX.contDiffAt_reciprocalParameter (n : WithTop ℕ∞) {y : Fin 2 → ℝ} (hy : y 0 + 1 ≠ 0) :
    ContDiffAt ℝ n reciprocalParameter y := by unfold reciprocalParameter; fun_prop

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_reciprocalParameterMap (n : WithTop ℕ∞) {y : Fin 2 → ℝ} (hy : y 0 + 1 ≠ 0) :
    ContDiffAt ℝ n reciprocalParameterMap y := by
  unfold reciprocalParameterMap
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_reciprocalParameter n hy
  · exact contDiffAt_apply ℝ ℝ 1 y

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.reciprocalParameter_fderiv {y : Fin 2 → ℝ} (hy : y 0 + 1 ≠ 0) (v : Fin 2 → ℝ) :
    fderiv ℝ reciprocalParameter y v = -(reciprocalParameter y) ^ 2 * v 0 := by
  have H := (hasFDerivAt_inv hy).comp y ((hasFDerivAt_apply (𝕜 := ℝ) 0 y).add_const 1)
  have H' := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L v) H.fderiv
  unfold reciprocalParameter
  simpa [Function.comp_def, reciprocalParameter, inv_pow, mul_comm] using H'

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.reciprocalParameter_fderiv2 {y : Fin 2 → ℝ} (hy : y 0 + 1 ≠ 0) (v w : Fin 2 → ℝ) :
    fderiv ℝ (fderiv ℝ reciprocalParameter) y v w = 2 * (reciprocalParameter y) ^ 3 * v 0 * w 0 := by
  have hreg := contDiffAt_reciprocalParameter 2 hy
  have hd := (hreg.differentiableAt (by norm_num)).hasFDerivAt
  have hd' := ((hreg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)).hasFDerivAt
  have Hleft := hd'.clm_apply (hasFDerivAt_const w y)
  have Hright := ((hd.pow 2).neg).mul_const (w 0)
  have heq : (fun z => fderiv ℝ reciprocalParameter z w) =ᶠ[𝓝 y]
      (fun z => -(reciprocalParameter z) ^ 2 * w 0) := by
    filter_upwards [((continuous_apply 0).add continuous_const).continuousAt.eventually_ne hy] with z hz
    exact reciprocalParameter_fderiv hz w
  have H := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L v)
    (Hleft.unique (Hright.congr_of_eventuallyEq heq))
  simpa [reciprocalParameter_fderiv hy, mul_assoc, mul_comm, mul_left_comm, pow_succ] using H

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.reciprocalParameterMap_fderiv {y : Fin 2 → ℝ} (hy : y 0 + 1 ≠ 0) (v : Fin 2 → ℝ) :
    fderiv ℝ reciprocalParameterMap y v = ![-(reciprocalParameter y) ^ 2 * v 0, v 1] := by
  have hd := (contDiffAt_reciprocalParameterMap 1 hy).differentiableAt (by norm_num)
  have H0 := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L v) (fderiv_apply hd (0 : Fin 2))
  have H1 := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L v) (fderiv_apply hd (1 : Fin 2))
  change fderiv ℝ reciprocalParameter y v = fderiv ℝ reciprocalParameterMap y v 0 at H0
  change fderiv ℝ (fun z : Fin 2 → ℝ => z 1) y v = fderiv ℝ reciprocalParameterMap y v 1 at H1
  rw [reciprocalParameter_fderiv hy] at H0
  rw [(hasFDerivAt_apply (𝕜 := ℝ) 1 y).fderiv] at H1
  ext i; fin_cases i
  · exact H0.symm
  · exact H1.symm

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.reciprocalParameterMap_fderiv2 {y : Fin 2 → ℝ} (hy : y 0 + 1 ≠ 0) (v w : Fin 2 → ℝ) :
    fderiv ℝ (fderiv ℝ reciprocalParameterMap) y v w = ![2 * (reciprocalParameter y) ^ 3 * v 0 * w 0, 0] := by
  have H0 := fderiv2_clm_comp_apply (contDiffAt_reciprocalParameterMap 2 hy)
    (ContinuousLinearMap.proj (0 : Fin 2)) v w
  have H1 := fderiv2_clm_comp_apply (contDiffAt_reciprocalParameterMap 2 hy)
    (ContinuousLinearMap.proj (1 : Fin 2)) v w
  change fderiv ℝ (fderiv ℝ reciprocalParameter) y v w = fderiv ℝ (fderiv ℝ reciprocalParameterMap) y v w 0 at H0
  change fderiv ℝ (fderiv ℝ (fun z : Fin 2 → ℝ => z 1)) y v w = fderiv ℝ (fderiv ℝ reciprocalParameterMap) y v w 1 at H1
  have hproj : fderiv ℝ (fun z : Fin 2 → ℝ => z 1) = fun _ => ContinuousLinearMap.proj 1 :=
    funext (fun z => (hasFDerivAt_apply (𝕜 := ℝ) 1 z).fderiv)
  rw [reciprocalParameter_fderiv2 hy] at H0
  rw [hproj, fderiv_const_apply] at H1
  ext i; fin_cases i
  · exact H0.symm
  · exact H1.symm

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.reciprocalParameter_range {y : Fin 2 → ℝ} (hy : 3 / 2 ≤ y 0) :
    0 < reciprocalParameter y ∧ reciprocalParameter y ≤ 2 / 5 := by
  have h : 0 < y 0 + 1 := by linarith
  refine ⟨inv_pos.mpr h, ?_⟩
  dsimp [reciprocalParameter]
  rw [← one_div]
  apply (div_le_iff₀ h).mpr
  linarith

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.reciprocalParameter_derivative_bounds {y : Fin 2 → ℝ} (hy : 3 / 2 ≤ y 0) (v w : Fin 2 → ℝ) :
    |fderiv ℝ reciprocalParameter y v| ≤ reciprocalParameter y * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ reciprocalParameter) y v w| ≤ 2 * reciprocalParameter y * ‖v‖ * ‖w‖ ∧
      ‖fderiv ℝ reciprocalParameterMap y v‖ ≤ ‖v‖ ∧
      ‖fderiv ℝ (fderiv ℝ reciprocalParameterMap) y v w‖ ≤ 2 * ‖v‖ * ‖w‖ := by
  let a := reciprocalParameter y
  have ha := reciprocalParameter_range hy
  have ha1 : a ≤ 1 := by dsimp [a]; linarith [ha.2]
  have ha0 : 0 ≤ a := ha.1.le
  have ha2 : a ^ 2 ≤ a := by nlinarith
  have ha3 : a ^ 3 ≤ a := by nlinarith [mul_le_mul_of_nonneg_left ha2 ha0]
  have hv (i : Fin 2) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hw (i : Fin 2) : |w i| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w i
  have hn : y 0 + 1 ≠ 0 := by linarith
  have H1 : |-(a ^ 2) * v 0| ≤ a * ‖v‖ := by
    rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg a)]
    exact mul_le_mul ha2 (hv 0) (abs_nonneg _) ha0
  have H2 : |2 * a ^ 3 * v 0 * w 0| ≤ 2 * a * ‖v‖ * ‖w‖ := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * a ^ 3)]
    exact mul_le_mul (mul_le_mul (by nlinarith : 2 * a ^ 3 ≤ 2 * a) (hv 0) (abs_nonneg _) (by positivity))
      (hw 0) (abs_nonneg _) (by positivity)
  refine ⟨by simpa only [reciprocalParameter_fderiv hn] using H1,
    by simpa only [reciprocalParameter_fderiv2 hn] using H2, ?_, ?_⟩
  · rw [reciprocalParameterMap_fderiv hn]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i; fin_cases i
    · exact H1.trans (mul_le_of_le_one_left (norm_nonneg v) ha1)
    · exact hv 1
  · rw [reciprocalParameterMap_fderiv2 hn]
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * ‖v‖ * ‖w‖)).mpr
    intro i; fin_cases i
    · exact H2.trans (by nlinarith only [mul_le_mul_of_nonneg_right ha1 (show 0 ≤ 2 * ‖v‖ * ‖w‖ by positivity)])
    · simpa using (show 0 ≤ 2 * ‖v‖ * ‖w‖ by positivity)

end
end

theorem solution {g : (Fin 2 → ℝ) → ℝ} {y : Fin 2 → ℝ} {B : ℝ}
    (hy : 3 / 2 ≤ y 0) (hB : 0 ≤ B)
    (hg : ContDiffAt ℝ 2 g (reciprocalParameterMap y))
    (hg0 : |g (reciprocalParameterMap y)| ≤ B)
    (hg1 : ‖fderiv ℝ g (reciprocalParameterMap y)‖ ≤ B)
    (hg2 : ‖fderiv ℝ (fderiv ℝ g) (reciprocalParameterMap y)‖ ≤ B) :
    |reciprocalParameter y * g (reciprocalParameterMap y)| ≤ B * reciprocalParameter y ∧
      ‖fderiv ℝ (fun z => reciprocalParameter z * g (reciprocalParameterMap z)) y‖ ≤
        2 * B * reciprocalParameter y ∧
      ‖fderiv ℝ (fderiv ℝ (fun z => reciprocalParameter z * g (reciprocalParameterMap z))) y‖ ≤
        7 * B * reciprocalParameter y := by
  let a := reciprocalParameter y
  let f := fun z => g (reciprocalParameterMap z)
  have ha : 0 ≤ a := (reciprocalParameter_range hy).1.le
  have hn : y 0 + 1 ≠ 0 := by linarith
  have haReg := contDiffAt_reciprocalParameter 2 hn
  have hpReg := contDiffAt_reciprocalParameterMap 2 hn
  have hfReg : ContDiffAt ℝ 2 f y := hg.comp y hpReg
  have hf1 (v : Fin 2 → ℝ) : |fderiv ℝ f y v| ≤ B * ‖v‖ := by
    have heq : fderiv ℝ f y v = fderiv ℝ g (reciprocalParameterMap y)
        (fderiv ℝ reciprocalParameterMap y v) := by
      rw [show f = g ∘ reciprocalParameterMap from rfl, fderiv_comp y
        (hg.differentiableAt (by norm_num)) (hpReg.differentiableAt (by norm_num))]
      rfl
    rw [heq]
    exact ((fderiv ℝ g (reciprocalParameterMap y)).le_opNorm _).trans
      (mul_le_mul hg1 (reciprocalParameter_derivative_bounds hy v v).2.2.1 (norm_nonneg _) hB)
  have hf2 (v w : Fin 2 → ℝ) : |fderiv ℝ (fderiv ℝ f) y v w| ≤ 3 * B * ‖v‖ * ‖w‖ := by
    rw [show f = g ∘ reciprocalParameterMap from rfl, fderiv2_comp_apply hpReg hg]
    have H1 := ((fderiv ℝ g (reciprocalParameterMap y)).le_opNorm
      (fderiv ℝ (fderiv ℝ reciprocalParameterMap) y v w)).trans
      (mul_le_mul hg1 (reciprocalParameter_derivative_bounds hy v w).2.2.2 (norm_nonneg _) hB)
    let L := fderiv ℝ (fderiv ℝ g) (reciprocalParameterMap y)
    have H2 := ((L (fderiv ℝ reciprocalParameterMap y v)).le_opNorm
      (fderiv ℝ reciprocalParameterMap y w)).trans
      (mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _))
    have H3 := mul_le_mul
      (mul_le_mul hg2 (reciprocalParameter_derivative_bounds hy v w).2.2.1 (norm_nonneg _) hB)
      (reciprocalParameter_derivative_bounds hy w v).2.2.1 (norm_nonneg _) (by positivity : 0 ≤ B * ‖v‖)
    have Hsum := abs_add_le
      (fderiv ℝ g (reciprocalParameterMap y) (fderiv ℝ (fderiv ℝ reciprocalParameterMap) y v w))
      (L (fderiv ℝ reciprocalParameterMap y v) (fderiv ℝ reciprocalParameterMap y w))
    simp only [Real.norm_eq_abs, L] at H1 H2 Hsum
    nlinarith only [H1, H2, H3, Hsum]
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_mul, abs_of_nonneg ha]
    nlinarith only [mul_le_mul_of_nonneg_left hg0 ha]
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [fderiv_fun_mul (haReg.differentiableAt (by norm_num)) (hfReg.differentiableAt (by norm_num))]
    change |reciprocalParameter y * fderiv ℝ f y v + f y * fderiv ℝ reciprocalParameter y v| ≤ _
    have H := abs_add_le (reciprocalParameter y * fderiv ℝ f y v) (f y * fderiv ℝ reciprocalParameter y v)
    rw [abs_mul, abs_mul, abs_of_nonneg ha] at H
    have H1 := mul_le_mul_of_nonneg_left (hf1 v) ha
    have H2 := mul_le_mul hg0 (reciprocalParameter_derivative_bounds hy v v).1 (abs_nonneg _) hB
    nlinarith only [H, H1, H2]
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    change |fderiv ℝ (fderiv ℝ (fun z => reciprocalParameter z * f z)) y v w| ≤ _
    rw [fderiv2_mul_apply haReg hfReg]
    have H0 := mul_le_mul_of_nonneg_left (hf2 v w) ha
    have H1 := mul_le_mul (reciprocalParameter_derivative_bounds hy v w).1 (hf1 w) (abs_nonneg _) (by positivity : 0 ≤ a * ‖v‖)
    have H2 := mul_le_mul (reciprocalParameter_derivative_bounds hy w v).1 (hf1 v) (abs_nonneg _) (by positivity : 0 ≤ a * ‖w‖)
    have H3 := mul_le_mul (reciprocalParameter_derivative_bounds hy v w).2.1 hg0 (abs_nonneg _) (by positivity : 0 ≤ 2 * a * ‖v‖ * ‖w‖)
    have htri (r s t u : ℝ) : |r + s + t + u| ≤ |r| + |s| + |t| + |u| := by
      linarith only [abs_add_le r s, abs_add_le (r + s) t, abs_add_le (r + s + t) u]
    have H := htri (a * fderiv ℝ (fderiv ℝ f) y v w)
      (fderiv ℝ reciprocalParameter y v * fderiv ℝ f y w)
      (fderiv ℝ reciprocalParameter y w * fderiv ℝ f y v)
      (fderiv ℝ (fderiv ℝ reciprocalParameter) y v w * f y)
    simp only [abs_mul, abs_of_nonneg ha] at H
    nlinarith only [H, H0, H1, H2, H3]
