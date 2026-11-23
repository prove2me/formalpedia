-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.radialMap_mem_cone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:26:36.036821+00:00
-- url     : https://prove2.me/submissions/14b2298f-2c12-4f9c-ab55-4f8b891016ac

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution (r : ℝ) (hr : 0 < r) {x : mixedSpace K}
    (hx : x ∈ mixedEmbedding.fundamentalCone K) :
    radialMap K r x ∈ mixedEmbedding.fundamentalCone K :=
  fundamentalCone.smul_mem_of_mem hx (Real.rpow_pos_of_pos hr _).ne'
end DedekindZeta.ConeRadialReduction
