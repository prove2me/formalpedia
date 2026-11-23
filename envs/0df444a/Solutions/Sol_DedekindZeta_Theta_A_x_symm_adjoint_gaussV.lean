-- Prove2me | solution 1 for DedekindZeta.Theta.A_x_symm_adjoint_gaussV
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:17:19.594809+00:00
-- url     : https://prove2.me/submissions/c6047b97-2239-4c5c-965f-9c738a74d548

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_toMinkowski_inner

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution {x : mixedEmbedding.mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) (w : minkowskiSpace K) :
    gaussV K (ContinuousLinearMap.adjoint
        ((A_x K hx).symm : minkowskiSpace K →L[ℝ] minkowskiSpace K) w)
      = gaussV K (toMinkowski K (x⁻¹ * (toMinkowski K).symm w)) := by
  classical
  -- Coordinatewise conjugate of `x⁻¹`: per place the adjoint of multiplication
  -- by `x_w` (w.r.t. the Minkowski inner product) is multiplication by `conj x_w`.
  set z : mixedEmbedding.mixedSpace K := conjMixed K x⁻¹ with hz
  -- Candidate adjoint of `(A_x).symm`: the `z`-scaling conjugated by `toMinkowski`.
  set B : minkowskiSpace K →L[ℝ] minkowskiSpace K :=
    (toMinkowski K : mixedEmbedding.mixedSpace K →L[ℝ] minkowskiSpace K).comp
      ((LinearMap.mulLeft ℝ z).toContinuousLinearMap.comp
        ((toMinkowski K).symm : minkowskiSpace K →L[ℝ] mixedEmbedding.mixedSpace K)) with hB
  have hBapp : ∀ v, B v = toMinkowski K (z * (toMinkowski K).symm v) := fun _ => rfl
  -- Explicit inverse of `A_x`.
  have hAsymm : ∀ v, (A_x K hx).symm v = toMinkowski K (x⁻¹ * (toMinkowski K).symm v) := by
    intro v
    rw [ContinuousLinearEquiv.symm_apply_eq, A_x_apply,
      ContinuousLinearEquiv.symm_apply_apply, ← mul_assoc,
      mul_inv_cancel_of_norm_ne_zero K hx, one_mul,
      ContinuousLinearEquiv.apply_symm_apply]
  -- `B` is the adjoint of `(A_x).symm`: the per-place adjoint identity.
  have hinner_eq : ∀ (u v : minkowskiSpace K),
      (inner ℝ ((A_x K hx).symm u) v : ℝ) = inner ℝ u (B v) := by
    intro u v
    have hu : u = toMinkowski K ((toMinkowski K).symm u) :=
      ((toMinkowski K).apply_symm_apply u).symm
    have hv : v = toMinkowski K ((toMinkowski K).symm v) :=
      ((toMinkowski K).apply_symm_apply v).symm
    rw [hAsymm u, hBapp v]
    conv_lhs => rw [hv]
    conv_rhs => rw [hu]
    rw [toMinkowski_inner, toMinkowski_inner]
    refine congr_arg₂ (· + ·) ?_ (congr_arg (fun s => 2 * s) ?_)
    · refine Finset.sum_congr rfl (fun w _ => ?_)
      simp only [Prod.fst_mul, Pi.mul_apply, hz, conjMixed_fst]
      ring
    · refine Finset.sum_congr rfl (fun w _ => ?_)
      congr 1
      simp only [Prod.snd_mul, Pi.mul_apply, hz, conjMixed_snd, map_mul, Complex.conj_conj]
      ring
  have hadj : ContinuousLinearMap.adjoint
      ((A_x K hx).symm : minkowskiSpace K →L[ℝ] minkowskiSpace K) = B := by
    have hAB : ((A_x K hx).symm : minkowskiSpace K →L[ℝ] minkowskiSpace K)
        = ContinuousLinearMap.adjoint B :=
      (ContinuousLinearMap.eq_adjoint_iff
        ((A_x K hx).symm : minkowskiSpace K →L[ℝ] minkowskiSpace K) B).2 hinner_eq
    rw [hAB, ContinuousLinearMap.adjoint_adjoint]
  -- `gaussV` depends only on the Minkowski norm; the two arguments have equal norm.
  have hns : (inner ℝ (toMinkowski K (z * (toMinkowski K).symm w))
        (toMinkowski K (z * (toMinkowski K).symm w)) : ℝ)
      = inner ℝ (toMinkowski K (x⁻¹ * (toMinkowski K).symm w))
        (toMinkowski K (x⁻¹ * (toMinkowski K).symm w)) := by
    rw [toMinkowski_inner, toMinkowski_inner]
    refine congr_arg₂ (· + ·) ?_ (congr_arg (fun s => 2 * s) ?_)
    · refine Finset.sum_congr rfl (fun w' _ => ?_)
      simp only [Prod.fst_mul, Pi.mul_apply, hz, conjMixed_fst]
    · refine Finset.sum_congr rfl (fun w' _ => ?_)
      rw [Complex.mul_conj, Complex.mul_conj, Complex.ofReal_re, Complex.ofReal_re]
      simp only [Prod.snd_mul, Pi.mul_apply, hz, conjMixed_snd, Complex.normSq_mul,
        Complex.normSq_conj]
  have hnorm2 : ‖toMinkowski K (z * (toMinkowski K).symm w)‖ ^ 2
      = ‖toMinkowski K (x⁻¹ * (toMinkowski K).symm w)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hns]
  rw [hadj, hBapp w]
  unfold gaussV
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, hnorm2]
end DedekindZeta.Theta
