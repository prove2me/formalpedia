-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.continuousOn_mixedThetaKernel_radialMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:43:12.7818+00:00
-- url     : https://prove2.me/submissions/96cebfae-46b6-45a9-a571-a03629cdb29a

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mapsTo_radialMap_closure_normEqOneSurface
import Theorems.Thm_DedekindZeta_Theta_continuousOn_mixedThetaKernel


set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (K)
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K)
    (r : ℝ) (hr : 0 < r) :
    ContinuousOn (fun σ => Theta.mixedThetaKernel K I (radialMap K r σ))
      (closure (normEqOneSurface K)) :=
  (Theta.continuousOn_mixedThetaKernel K I).comp
    (continuous_const_smul (r ^ ((finrank ℚ K : ℝ)⁻¹))).continuousOn
    (mapsTo_radialMap_closure_normEqOneSurface K r hr)
end DedekindZeta.ConeRadialReduction
