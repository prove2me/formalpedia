-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.aestronglyMeasurable_mixedGaussian_mul_norm_cpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:28:35.200887+00:00
-- url     : https://prove2.me/submissions/0b9e5adb-cda3-45e0-922e-81fb633c5199

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
variable {K}
namespace DedekindZeta.GammaIntegral
theorem _root_.solution (s : ℂ)
    (c : mixedEmbedding.mixedSpace K) :
    AEStronglyMeasurable
      (fun y : mixedEmbedding.mixedSpace K =>
        (mixedGaussian K y : ℂ) * (mixedEmbedding.norm (y * c) : ℂ) ^ s)
      (mixedMulHaar K) := by
  -- A Borel-measurable function into a second-countable space is
  -- `AEStronglyMeasurable` against any measure.
  apply Measurable.aestronglyMeasurable
  apply Measurable.mul
  · refine Complex.measurable_ofReal.comp ?_
    unfold mixedGaussian
    fun_prop
  · refine (Complex.measurable_ofReal.comp ?_).pow_const s
    exact (mixedEmbedding.continuous_norm K).measurable.comp
      (continuous_id.mul continuous_const).measurable
end DedekindZeta.GammaIntegral
