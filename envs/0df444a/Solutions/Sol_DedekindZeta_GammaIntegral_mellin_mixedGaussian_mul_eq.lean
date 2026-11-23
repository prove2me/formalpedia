-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.mellin_mixedGaussian_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:33:42.33169+00:00
-- url     : https://prove2.me/submissions/90e02255-928a-4a13-8ab1-35e4d9237b3b

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_mixedEmbedding_norm_inv
import Theorems.Thm_DedekindZeta_ofReal_inv_cpow
import Theorems.Thm_DedekindZeta_GammaIntegral_mixedEmbedding_norm_eq_absNorm_span
import Theorems.Thm_DedekindZeta_GammaIntegral_norm_mixedEmbedding_ne_zero
import Theorems.Thm_DedekindZeta_GammaIntegral_aestronglyMeasurable_mixedGaussian_mul_norm_cpow
import Theorems.Thm_DedekindZeta_GammaIntegral_mulHaar_integral_comp_mul_right
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta DedekindZeta.GammaIntegral
open DedekindZeta DedekindZeta.Theta
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
variable {K}
namespace DedekindZeta.GammaIntegral
theorem _root_.solution (s : ℂ) {a : 𝓞 K} (ha : a ≠ 0) :
    ∫ x, (mixedGaussian K (x * mixedEmbedding K ((a : 𝓞 K) : K)) : ℂ)
            * (mixedEmbedding.norm x : ℂ) ^ s ∂(mixedMulHaar K)
      = (Ideal.absNorm (Ideal.span {a}) : ℂ) ^ (-s) * I K s := by
  set c : mixedEmbedding.mixedSpace K := mixedEmbedding K ((a : 𝓞 K) : K) with hcdef
  have hcne : mixedEmbedding.norm c ≠ 0 := norm_mixedEmbedding_ne_zero ha
  have hcinv : mixedEmbedding.norm c⁻¹ ≠ 0 := by
    rw [mixedEmbedding_norm_inv]; exact inv_ne_zero hcne
  have hcc : c * c⁻¹ = 1 := Theta.mul_inv_cancel_of_norm_ne_zero K hcne
  have hnc : mixedEmbedding.norm c = (Ideal.absNorm (Ideal.span {a}) : ℝ) := by
    rw [hcdef]; exact mixedEmbedding_norm_eq_absNorm_span K a
  -- The integrand as `F (x * c)` with `F y = g y · |N(y·c⁻¹)|^s`.
  set F : mixedEmbedding.mixedSpace K → ℂ :=
    fun y => (mixedGaussian K y : ℂ) * (mixedEmbedding.norm (y * c⁻¹) : ℂ) ^ s with hFdef
  have hFmeas : AEStronglyMeasurable F (mixedMulHaar K) :=
    aestronglyMeasurable_mixedGaussian_mul_norm_cpow s c⁻¹
  have hrw : (fun x => (mixedGaussian K (x * c) : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s)
      = fun x => F (x * c) := by
    funext x
    simp only [hFdef, mul_assoc, hcc, mul_one]
  calc
    ∫ x, (mixedGaussian K (x * c) : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s ∂(mixedMulHaar K)
        = ∫ x, F (x * c) ∂(mixedMulHaar K) := by rw [hrw]
      _ = ∫ y, F y ∂(mixedMulHaar K) :=
          mulHaar_integral_comp_mul_right F hcne hFmeas
      _ = ∫ y, ((mixedGaussian K y : ℂ) * (mixedEmbedding.norm y : ℂ) ^ s)
              * ((Ideal.absNorm (Ideal.span {a}) : ℂ) ^ (-s)) ∂(mixedMulHaar K) := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
          simp only [hFdef]
          rw [map_mul mixedEmbedding.norm y c⁻¹, mixedEmbedding_norm_inv,
            Complex.ofReal_mul,
            Complex.mul_cpow_ofReal_nonneg (mixedEmbedding.norm_nonneg y)
              (inv_nonneg.mpr (mixedEmbedding.norm_nonneg c)),
            ofReal_inv_cpow (mixedEmbedding.norm_nonneg c) s, hnc]
          push_cast
          ring
      _ = (∫ y, (mixedGaussian K y : ℂ) * (mixedEmbedding.norm y : ℂ) ^ s ∂(mixedMulHaar K))
              * ((Ideal.absNorm (Ideal.span {a}) : ℂ) ^ (-s)) :=
          integral_mul_const _ _
      _ = (Ideal.absNorm (Ideal.span {a}) : ℂ) ^ (-s) * I K s := by
          rw [mul_comm]; rfl
end DedekindZeta.GammaIntegral
