-- Prove2me | solution 1 for DedekindZeta.mulHaar_integral_comp_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:38:41.174796+00:00
-- url     : https://prove2.me/submissions/3f790942-0e0f-4714-876e-d374bbebeddd

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_mixedMulHaar_map_inv
import Theorems.Thm_DedekindZeta_measurable_mixedSpace_inv

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
variable {K : Type*} [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta
theorem _root_.solution (g : mixedEmbedding.mixedSpace K → ℂ)
    (hg : AEStronglyMeasurable g (mixedMulHaar K)) :
    ∫ x, g x ∂(mixedMulHaar K) = ∫ x, g x⁻¹ ∂(mixedMulHaar K) := by
  have hmap := mixedMulHaar_map_inv (K := K)
  calc ∫ x, g x ∂(mixedMulHaar K)
      = ∫ x, g x ∂(Measure.map (fun x => x⁻¹) (mixedMulHaar K)) := by rw [hmap]
    _ = ∫ x, g x⁻¹ ∂(mixedMulHaar K) :=
        integral_map measurable_mixedSpace_inv.aemeasurable (hmap.symm ▸ hg)
end DedekindZeta
