-- Prove2me | solution 1 for DedekindZeta.Theta.det_scaleMixed_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:19:16.712279+00:00
-- url     : https://prove2.me/submissions/32272e2a-dfc7-4655-9e92-386cf8a44b2d

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_scaleMixed_symm_apply
import Theorems.Thm_DedekindZeta_Theta_finrank_complexPart
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open Module
namespace DedekindZeta.Theta
theorem _root_.solution :
    LinearMap.det ((scaleMixed K).symm.toLinearEquiv.toLinearMap :
        mixedSpace K →ₗ[ℝ] mixedSpace K)
      = ((Real.sqrt 2)⁻¹) ^ (2 * nrComplexPlaces K) := by
  have hform : LinearMap.prodMap LinearMap.id
          (((Real.sqrt 2)⁻¹) • (LinearMap.id :
            ({w : InfinitePlace K // InfinitePlace.IsComplex w} → ℂ) →ₗ[ℝ] _))
      = ((scaleMixed K).symm.toLinearEquiv.toLinearMap :
          mixedSpace K →ₗ[ℝ] mixedSpace K) := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.prodMap_apply, LinearMap.id_coe, id_eq, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq]
    show (x.1, (Real.sqrt 2)⁻¹ • x.2) = (scaleMixed K).symm x
    rw [scaleMixed_symm_apply]
  rw [← hform, LinearMap.det_prodMap, LinearMap.det_id, one_mul, LinearMap.det_smul,
    LinearMap.det_id, mul_one, finrank_complexPart]
end DedekindZeta.Theta
