-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.measurable_mixedGaussian_comp_mul_norm_cpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:47:11.718063+00:00
-- url     : https://prove2.me/submissions/b3967f20-fd18-45db-a97d-4513cc060e1f

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral

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
open scoped nonZeroDivisors
variable {K}
namespace DedekindZeta.GammaIntegral
theorem _root_.solution (s : ℂ)
    (c : mixedEmbedding.mixedSpace K) :
    Measurable
      (fun x : mixedEmbedding.mixedSpace K =>
        (mixedGaussian K (x * c) : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s) := by
  apply Measurable.mul
  · refine Complex.measurable_ofReal.comp ?_
    unfold mixedGaussian
    fun_prop
  · exact (Complex.measurable_ofReal.comp
      (mixedEmbedding.continuous_norm K).measurable).pow_const s
end DedekindZeta.GammaIntegral
