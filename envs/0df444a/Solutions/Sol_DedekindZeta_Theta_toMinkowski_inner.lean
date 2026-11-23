-- Prove2me | solution 1 for DedekindZeta.Theta.toMinkowski_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:14:25.83351+00:00
-- url     : https://prove2.me/submissions/c3976ca8-3a6e-4551-a504-9261bc5c8da7

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
theorem _root_.solution (p q : mixedEmbedding.mixedSpace K) :
    (inner ℝ (toMinkowski K p) (toMinkowski K q) : ℝ) =
      (∑ w : {w : InfinitePlace K // w.IsReal}, (p.1 w) * (q.1 w)) +
      2 * ∑ w : {w : InfinitePlace K // w.IsComplex},
          ((p.2 w) * (starRingEnd ℂ) (q.2 w)).re := by
  classical
  rw [toMinkowski, WithLp.prod_inner_apply,
      show (WithLp.ofLp ((ContinuousLinearEquiv.trans (scaleMixed K)
          (mixedEmbedding.euclidean.toMixed K).symm) p)).fst
          = WithLp.toLp 2 (scaleMixed K p).1 from rfl,
      show (WithLp.ofLp ((ContinuousLinearEquiv.trans (scaleMixed K)
          (mixedEmbedding.euclidean.toMixed K).symm) p)).snd
          = WithLp.toLp 2 (scaleMixed K p).2 from rfl,
      show (WithLp.ofLp ((ContinuousLinearEquiv.trans (scaleMixed K)
          (mixedEmbedding.euclidean.toMixed K).symm) q)).fst
          = WithLp.toLp 2 (scaleMixed K q).1 from rfl,
      show (WithLp.ofLp ((ContinuousLinearEquiv.trans (scaleMixed K)
          (mixedEmbedding.euclidean.toMixed K).symm) q)).snd
          = WithLp.toLp 2 (scaleMixed K q).2 from rfl]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, scaleMixed,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.coe_refl', id_eq,
    ContinuousLinearEquiv.smulLeft_apply_apply, real_inner_eq_re_inner ℂ]
  rw [Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun w _ => ?_)
    ring
  · refine Finset.sum_congr rfl (fun w _ => ?_)
    have hz : (sqrtTwo • q.2) w * (starRingEnd ℂ) ((sqrtTwo • p.2) w)
        = (↑(2:ℝ) : ℂ) * (q.2 w * (starRingEnd ℂ) (p.2 w)) := by
      simp only [Pi.smul_apply, Units.smul_def, sqrtTwo, Units.val_mk0, Complex.real_smul,
        map_mul, Complex.conj_ofReal]
      have h2 : (↑(Real.sqrt 2) : ℂ) * (↑(Real.sqrt 2) : ℂ) = (↑(2:ℝ) : ℂ) := by
        norm_cast; exact Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
      linear_combination (q.2 w * (starRingEnd ℂ) (p.2 w)) * h2
    rw [hz]
    simp only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im]
    ring
end DedekindZeta.Theta
