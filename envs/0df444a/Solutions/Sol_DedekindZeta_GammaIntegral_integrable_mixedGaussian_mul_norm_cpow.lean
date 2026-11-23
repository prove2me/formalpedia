-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.integrable_mixedGaussian_mul_norm_cpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:40:13.89084+00:00
-- url     : https://prove2.me/submissions/6f7195ab-31f5-45fd-9007-324a84bde8a3

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_GammaIntegral_integrable_gaussian_mellin
import Theorems.Thm_DedekindZeta_mixedEmbedding_norm_inv
import Theorems.Thm_DedekindZeta_ofReal_inv_cpow
import Theorems.Thm_DedekindZeta_GammaIntegral_mixedEmbedding_norm_eq_absNorm_span
import Theorems.Thm_DedekindZeta_GammaIntegral_norm_mixedEmbedding_ne_zero
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_measurable_mul_right_mixedSpace
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
set_option maxHeartbeats 1000000
variable {K}
namespace DedekindZeta.GammaIntegral
theorem _root_.solution (s : ℂ) (hs : 1 < s.re)
    {a : 𝓞 K} (ha : a ≠ 0) :
    Integrable
      (fun x : mixedEmbedding.mixedSpace K =>
        (mixedGaussian K (x * mixedEmbedding K ((a : 𝓞 K) : K)) : ℂ)
          * (mixedEmbedding.norm x : ℂ) ^ s)
      (mixedMulHaar K) := by
  have hs0 : (0 : ℝ) < s.re := lt_trans one_pos hs
  set c : mixedEmbedding.mixedSpace K := mixedEmbedding K ((a : 𝓞 K) : K) with hcdef
  have hcne : mixedEmbedding.norm c ≠ 0 := norm_mixedEmbedding_ne_zero ha
  have hcc : c * c⁻¹ = 1 := Theta.mul_inv_cancel_of_norm_ne_zero K hcne
  have hnc : mixedEmbedding.norm c = (Ideal.absNorm (Ideal.span {a}) : ℝ) := by
    rw [hcdef]; exact mixedEmbedding_norm_eq_absNorm_span K a
  -- The integrand as `F (x * c)` with `F y = g y · |N(y·c⁻¹)|^s`.
  set F : mixedEmbedding.mixedSpace K → ℂ :=
    fun y => (mixedGaussian K y : ℂ) * (mixedEmbedding.norm (y * c⁻¹) : ℂ) ^ s with hFdef
  -- `F` factors as the basic Mellin integrand times the constant `𝔑((a))^{-s}`.
  have hFeq : F = fun y => ((mixedGaussian K y : ℂ) * (mixedEmbedding.norm y : ℂ) ^ s)
      * ((Ideal.absNorm (Ideal.span {a}) : ℂ) ^ (-s)) := by
    funext y
    simp only [hFdef]
    rw [map_mul mixedEmbedding.norm y c⁻¹, mixedEmbedding_norm_inv,
      Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (mixedEmbedding.norm_nonneg y)
        (inv_nonneg.mpr (mixedEmbedding.norm_nonneg c)),
      ofReal_inv_cpow (mixedEmbedding.norm_nonneg c) s, hnc]
    push_cast
    ring
  -- The basic Mellin integrand is integrable by `integrable_gaussian_mellin`
  -- (defeq through `mixedGaussian = gaussian`, `mixedMulHaar = mulHaar`).
  have hbase : Integrable
      (fun y : mixedEmbedding.mixedSpace K =>
        (mixedGaussian K y : ℂ) * (mixedEmbedding.norm y : ℂ) ^ s) (mixedMulHaar K) :=
    integrable_gaussian_mellin K hs0
  have hFint : Integrable F (mixedMulHaar K) := by
    rw [hFeq]; exact hbase.mul_const _
  -- Right translation `x ↦ x · c` is measure-preserving for `mixedMulHaar`.
  have hmp : MeasurePreserving (fun x : mixedEmbedding.mixedSpace K => x * c)
      (mixedMulHaar K) (mixedMulHaar K) :=
    ⟨measurable_mul_right_mixedSpace K c, mixedMulHaar_map_mul_right K hcne⟩
  have hrw : (fun x => (mixedGaussian K (x * c) : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s)
      = fun x => F (x * c) := by
    funext x
    simp only [hFdef, mul_assoc, hcc, mul_one]
  rw [hrw]
  exact hmp.integrable_comp_of_integrable hFint
end DedekindZeta.GammaIntegral
