-- Prove2me | solution 1 for DedekindZeta.Theta.A_x_det_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:14:40.687131+00:00
-- url     : https://prove2.me/submissions/873e0a77-021d-4466-80fa-45f1e87acb5e

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
theorem _root_.solution {x : mixedEmbedding.mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
    |LinearMap.det ((A_x K hx).toLinearEquiv : minkowskiSpace K →ₗ[ℝ] minkowskiSpace K)|
      = |mixedEmbedding.norm x| := by
  -- Step 1: conjugation by `toMinkowski` does not change the determinant, so
  -- `det (A_x) = det (mulLeft ℝ x)` on `mixedSpace K`.
  have hconj : ((A_x K hx).toLinearEquiv : minkowskiSpace K →ₗ[ℝ] minkowskiSpace K)
      = ((toMinkowski K).toLinearEquiv : mixedSpace K →ₗ[ℝ] minkowskiSpace K) ∘ₗ
          (LinearMap.mulLeft ℝ x) ∘ₗ
          ((toMinkowski K).toLinearEquiv.symm : minkowskiSpace K →ₗ[ℝ] mixedSpace K) := by
    refine LinearMap.ext fun v => ?_
    simp [A_x_apply, LinearMap.mulLeft_apply]
  rw [hconj, LinearMap.det_conj]
  -- Step 2: `mulLeft ℝ x` is block-diagonal across the real/complex factors.
  have hprod : LinearMap.mulLeft ℝ x
      = LinearMap.prodMap (LinearMap.mulLeft ℝ x.1) (LinearMap.mulLeft ℝ x.2) := by
    refine LinearMap.ext fun v => ?_
    apply Prod.ext <;> simp [LinearMap.mulLeft_apply, Prod.fst_mul, Prod.snd_mul]
  -- Real block: a diagonal map with determinant `∏_w x.1 w`.
  have hdetR : LinearMap.det (LinearMap.mulLeft ℝ x.1) = ∏ w, x.1 w := by
    have hR : LinearMap.mulLeft ℝ x.1
        = LinearMap.pi (fun w => (LinearMap.mulLeft ℝ (x.1 w)).comp (LinearMap.proj w)) := by
      refine LinearMap.ext fun v => ?_
      funext w
      simp [LinearMap.mulLeft_apply, Pi.mul_apply]
    rw [hR, LinearMap.det_pi]
    simp_rw [LinearMap.det_mulLeft]
  -- Complex block: per place the `ℝ`-linear determinant of `mulLeft (x.2 w)` on `ℂ`
  -- is `Algebra.norm ℝ (x.2 w) = normSq (x.2 w) = ‖x.2 w‖²`.
  have hdetC : LinearMap.det (LinearMap.mulLeft ℝ x.2) = ∏ w, ‖x.2 w‖ ^ 2 := by
    have hC : LinearMap.mulLeft ℝ x.2
        = LinearMap.pi (fun w => (LinearMap.mulLeft ℝ (x.2 w)).comp (LinearMap.proj w)) := by
      refine LinearMap.ext fun v => ?_
      funext w
      simp [LinearMap.mulLeft_apply, Pi.mul_apply]
    rw [hC, LinearMap.det_pi]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hlmul : LinearMap.mulLeft ℝ (x.2 w) = Algebra.lmul ℝ ℂ (x.2 w) := by
      ext y
      simp [LinearMap.mulLeft_apply, Algebra.coe_lmul_eq_mul]
    rw [hlmul, ← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  -- Step 3: assemble `|det| = (∏_real |x.1 w|)·(∏_complex ‖x.2 w‖²) = |N(x)|`.
  have hreal : (∏ w : {w : InfinitePlace K // InfinitePlace.IsReal w},
        normAtPlace w.1 x ^ InfinitePlace.mult w.1)
      = ∏ w : {w : InfinitePlace K // InfinitePlace.IsReal w}, ‖x.1 w‖ :=
    Finset.prod_congr rfl fun w _ => by
      rw [InfinitePlace.mult_isReal, pow_one, normAtPlace_apply_of_isReal w.prop]
  have hcpx : (∏ w : {w : InfinitePlace K // InfinitePlace.IsComplex w},
        normAtPlace w.1 x ^ InfinitePlace.mult w.1)
      = ∏ w : {w : InfinitePlace K // InfinitePlace.IsComplex w}, ‖x.2 w‖ ^ 2 :=
    Finset.prod_congr rfl fun w _ => by
      rw [InfinitePlace.mult_isComplex, normAtPlace_apply_of_isComplex w.prop]
  have hn : mixedEmbedding.norm x
      = (∏ w : {w : InfinitePlace K // InfinitePlace.IsReal w}, ‖x.1 w‖)
        * (∏ w : {w : InfinitePlace K // InfinitePlace.IsComplex w}, ‖x.2 w‖ ^ 2) := by
    rw [mixedEmbedding.norm_apply, InfinitePlace.prod_eq_prod_mul_prod, hreal, hcpx]
  rw [hprod, LinearMap.det_prodMap, hdetR, hdetC, abs_mul, Finset.abs_prod,
    _root_.abs_of_nonneg (Finset.prod_nonneg fun w _ => sq_nonneg _),
    _root_.abs_of_nonneg (mixedEmbedding.norm_nonneg x), hn]
  congr 1
end DedekindZeta.Theta
