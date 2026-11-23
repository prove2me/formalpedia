-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.mulHaar_integral_comp_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:30:37.697716+00:00
-- url     : https://prove2.me/submissions/c1509bb2-7efe-445e-9663-fda1e9b35380

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_measurable_mul_right_mixedSpace


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
theorem _root_.solution (g : mixedEmbedding.mixedSpace K → ℂ)
    {c : mixedEmbedding.mixedSpace K} (hc : mixedEmbedding.norm c ≠ 0)
    (hg : AEStronglyMeasurable g (mixedMulHaar K)) :
    ∫ x, g (x * c) ∂(mixedMulHaar K) = ∫ x, g x ∂(mixedMulHaar K) := by
  have hmap := mixedMulHaar_map_mul_right (K := K) hc
  calc ∫ x, g (x * c) ∂(mixedMulHaar K)
      = ∫ y, g y ∂(Measure.map (fun x => x * c) (mixedMulHaar K)) :=
        (integral_map (measurable_mul_right_mixedSpace K c).aemeasurable
          (hmap.symm ▸ hg)).symm
    _ = ∫ y, g y ∂(mixedMulHaar K) := by rw [hmap]
end DedekindZeta.GammaIntegral
