-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.norm_mixedEmbedding_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:46:52.56692+00:00
-- url     : https://prove2.me/submissions/40e23796-a779-4afd-8482-bc10b10d3b35

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_GammaIntegral_mixedEmbedding_norm_eq_absNorm_span
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
theorem _root_.solution {a : 𝓞 K} (ha : a ≠ 0) :
    mixedEmbedding.norm (mixedEmbedding K ((a : 𝓞 K) : K)) ≠ 0 := by
  rw [mixedEmbedding_norm_eq_absNorm_span]
  have : Ideal.span {a} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using ha
  exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr this)
end DedekindZeta.GammaIntegral
