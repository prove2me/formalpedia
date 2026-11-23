-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.radialProj_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:44:42.651829+00:00
-- url     : https://prove2.me/submissions/35774ed5-1a66-4f6b-b852-986ef8ba0d17

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_radialMap_inv
import Theorems.Thm_DedekindZeta_mixedEmbedding_norm_inv


set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
    (radialProj K x)⁻¹ = radialProj K x⁻¹ := by
  have hpos : 0 < mixedEmbedding.norm x :=
    (mixedEmbedding.norm_nonneg x).lt_of_ne (Ne.symm hx)
  have hinvpos : 0 < (mixedEmbedding.norm x)⁻¹ := inv_pos.mpr hpos
  rw [radialProj, radialProj, DedekindZeta.mixedEmbedding_norm_inv,
    ← radialMap_inv (mixedEmbedding.norm x)⁻¹ hinvpos x, one_div]
end DedekindZeta.ConeRadialReduction
