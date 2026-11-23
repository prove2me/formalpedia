-- Prove2me | solution 1 for DedekindZeta.Theta.mixedGaussian_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:13:32.347806+00:00
-- url     : https://prove2.me/submissions/30f92fce-aeaf-4229-9b4e-e94b40e55fb7

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (x : mixedEmbedding.mixedSpace K) :
    (mixedGaussian K x : ℂ) = gaussV K (toMinkowski K x) := by
  classical
  -- `(conj z · z).re = ‖z‖²` on `ℂ`, used on each complex place.
  have hre : ∀ z : ℂ, ((starRingEnd ℂ) z * z).re = ‖z‖ ^ 2 := by
    intro z
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  -- General-point analog of `inner_eEmb`: the Minkowski inner product of
  -- `toMinkowski K x` with itself expands over the real/complex places, the
  -- `√2`-weighting (`scaleMixed`) putting the factor `2` on the complex places.
  have hinner : (inner ℝ (toMinkowski K x) (toMinkowski K x) : ℝ) =
      (∑ w : {w : InfinitePlace K // w.IsReal}, (x.1 w) * (x.1 w)) +
      2 * ∑ w : {w : InfinitePlace K // w.IsComplex},
          ((starRingEnd ℂ) (x.2 w) * (x.2 w)).re := by
    rw [toMinkowski, WithLp.prod_inner_apply,
        show (WithLp.ofLp ((ContinuousLinearEquiv.trans (scaleMixed K)
            (mixedEmbedding.euclidean.toMixed K).symm) x)).fst
            = WithLp.toLp 2 (scaleMixed K x).1 from rfl,
        show (WithLp.ofLp ((ContinuousLinearEquiv.trans (scaleMixed K)
            (mixedEmbedding.euclidean.toMixed K).symm) x)).snd
            = WithLp.toLp 2 (scaleMixed K x).2 from rfl]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, scaleMixed,
      ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.coe_refl', id_eq,
      ContinuousLinearEquiv.smulLeft_apply_apply, real_inner_eq_re_inner ℂ]
    rw [Finset.mul_sum]
    -- The complex-place summand identity (the `√2`-weighting gives the factor `2`).
    have hcplx : ∀ w : {w : InfinitePlace K // w.IsComplex},
        RCLike.re ((sqrtTwo • x.2) w * (starRingEnd ℂ) ((sqrtTwo • x.2) w))
          = 2 * ((starRingEnd ℂ) (x.2 w) * x.2 w).re := by
      intro w
      have hnorm : ‖(sqrtTwo • x.2) w‖ = Real.sqrt 2 * ‖x.2 w‖ := by
        rw [Pi.smul_apply, Units.smul_def, _root_.norm_smul, sqrtTwo, Units.val_mk0,
          Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
      -- LHS: `RCLike.re (z * conj z) = ‖z‖² = 2‖x.2 w‖²` with `z = (√2 • x.2) w`;
      -- RHS rewritten by `hre`.
      rw [RCLike.mul_conj, RCLike.re_ofReal_pow, hnorm, mul_pow,
        Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), hre]
    rw [Finset.sum_congr rfl (fun w (_ : w ∈ Finset.univ) => hcplx w)]
  -- Hence the Minkowski norm-squared is the Minkowski quadratic form.
  have hnorm2 : ‖toMinkowski K x‖ ^ 2 =
      ∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ) * normAtPlace w x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hinner, InfinitePlace.sum_eq_sum_add_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [InfinitePlace.mult_isReal, normAtPlace_apply_of_isReal w.2]
      push_cast; rw [Real.norm_eq_abs, sq_abs]; ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [InfinitePlace.mult_isComplex, normAtPlace_apply_of_isComplex w.2, hre]
      push_cast; ring
  -- Push the real Gaussian through `Complex.ofReal_exp` and substitute.
  rw [mixedGaussian, gaussV, Complex.ofReal_exp]
  congr 1
  rw [← hnorm2]
  push_cast; ring
end DedekindZeta.Theta
