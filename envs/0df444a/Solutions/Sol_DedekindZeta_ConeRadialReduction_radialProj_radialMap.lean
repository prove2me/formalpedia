-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.radialProj_radialMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:42:29.907395+00:00
-- url     : https://prove2.me/submissions/d163514d-a814-44d3-961c-36047942430f

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_norm_radialMap
import Theorems.Thm_DedekindZeta_ConeRadialReduction_radialMap_radialMap

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution {t : ℝ} (ht : 0 < t) (x : mixedSpace K) :
    radialProj K (radialMap K t x) = radialProj K x := by
  rw [radialProj, norm_radialMap t ht x,
    radialMap_radialMap _ t
      (inv_nonneg.mpr (mul_nonneg ht.le (mixedEmbedding.norm_nonneg x))) ht.le,
    radialProj]
  congr 1
  rw [mul_comm ((t * mixedEmbedding.norm x)⁻¹) t, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ ht.ne', one_mul]
end DedekindZeta.ConeRadialReduction
