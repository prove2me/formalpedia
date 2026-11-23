-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.mixedQuadForm_radialMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:37:33.828408+00:00
-- url     : https://prove2.me/submissions/f1edadb8-14db-485e-a91e-c541eb363ce4

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedQuadForm_smul

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution (r : ℝ) (hr : 0 < r) (y : mixedSpace K) :
    mixedQuadForm K (radialMap K r y)
      = r ^ (2 * (finrank ℚ K : ℝ)⁻¹) * mixedQuadForm K y := by
  rw [radialMap, mixedQuadForm_smul]
  congr 1
  rw [mul_comm (2 : ℝ), Real.rpow_mul hr.le,
    ← Real.rpow_natCast (r ^ ((finrank ℚ K : ℝ)⁻¹)) 2]
  norm_num
end DedekindZeta.ConeRadialReduction
