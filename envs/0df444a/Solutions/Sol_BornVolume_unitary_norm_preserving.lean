-- Prove2me | solution 1 for BornVolume.unitary_norm_preserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:59:56.530739+00:00
-- url     : https://prove2.me/submissions/4f8e982c-50a6-4705-84d4-a60038541ad3

module
public import Definitions.Def_BornVolumeLean_Volume_MomentMeasurable
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudy
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Definitions.Def_BornVolumeLean_Volume_GaussianFS
public import Theorems.Thm_BornVolume_euclidean_norm_sq_eq_sum


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization
open BornVolume
variable {N : ℕ}
namespace BornVolume
theorem _root_.solution (U : Matrix.unitaryGroup (Fin N) ℂ)
    (v : EuclideanSpace ℂ (Fin N)) :
    ‖(Matrix.toEuclideanLin U.val) v‖ = ‖v‖ := by
  have hUU : U.valᴴ * U.val = 1 := by
    have h := U.2
    rw [Matrix.mem_unitaryGroup_iff'] at h
    rwa [Matrix.star_eq_conjTranspose] at h
  have hL : ∀ (w : Fin N → ℂ), ∑ i, ‖w i‖ ^ 2 = (star w ⬝ᵥ w).re := by
    intro w
    rw [dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, RCLike.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
        ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have key : star (U.val *ᵥ WithLp.ofLp v) ⬝ᵥ (U.val *ᵥ WithLp.ofLp v)
      = star (WithLp.ofLp v) ⬝ᵥ WithLp.ofLp v := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hUU,
        Matrix.one_mulVec]
  have hsq : ‖(Matrix.toEuclideanLin U.val) v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [euclidean_norm_sq_eq_sum, euclidean_norm_sq_eq_sum]
    show ∑ i, ‖(U.val *ᵥ WithLp.ofLp v) i‖ ^ 2 = ∑ i, ‖WithLp.ofLp v i‖ ^ 2
    rw [hL (U.val *ᵥ WithLp.ofLp v), hL (WithLp.ofLp v), key]
  have h1 : 0 ≤ ‖(Matrix.toEuclideanLin U.val) v‖ := norm_nonneg _
  have h2 : 0 ≤ ‖v‖ := norm_nonneg _
  nlinarith [hsq, h1, h2]
end BornVolume
