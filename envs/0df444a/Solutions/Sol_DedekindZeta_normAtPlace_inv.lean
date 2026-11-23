-- Prove2me | solution 1 for DedekindZeta.normAtPlace_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:28:12.464508+00:00
-- url     : https://prove2.me/submissions/98467906-a8c7-4867-b55d-5edbe92a7b83

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral

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
theorem _root_.solution (w : InfinitePlace K) (x : mixedEmbedding.mixedSpace K) :
    normAtPlace w x⁻¹ = (normAtPlace w x)⁻¹ := by
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_of_isReal hw, normAtPlace_apply_of_isReal hw,
      show x⁻¹.1 ⟨w, hw⟩ = (x.1 ⟨w, hw⟩)⁻¹ from rfl, norm_inv]
  · rw [normAtPlace_apply_of_isComplex hw, normAtPlace_apply_of_isComplex hw,
      show x⁻¹.2 ⟨w, hw⟩ = (x.2 ⟨w, hw⟩)⁻¹ from rfl, norm_inv]
end DedekindZeta
