-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.coneMellin_idealThetaKernel_eq_radial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:46:57.578566+00:00
-- url     : https://prove2.me/submissions/9e8e7df4-1e23-4d26-84e0-84eea9373656

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_measurableSet_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_norm_radialMap_of_mem
import Theorems.Thm_DedekindZeta_ConeRadialReduction_setIntegral_cone_eq_radial

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (s : ℂ)
    (hh : IntegrableOn
        (fun x => Theta.idealThetaKernel K 𝔞 x * (mixedEmbedding.norm x : ℂ) ^ s)
        (mixedEmbedding.fundamentalCone K) (DedekindZeta.mixedMulHaar K)) :
    ∫ x in mixedEmbedding.fundamentalCone K,
        Theta.idealThetaKernel K 𝔞 x * (mixedEmbedding.norm x : ℂ) ^ s
          ∂(DedekindZeta.mixedMulHaar K)
      = ∫ r in Set.Ioi (0 : ℝ),
          orbitTheta K 𝔞 r * (r : ℂ) ^ s * (r : ℝ)⁻¹ ∂volume := by
  rw [setIntegral_cone_eq_radial _ hh]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr0 : (0 : ℝ) < r := hr
  -- Inner surface integral: factor `N(radialMap K r σ)^s = r^s` out of the
  -- `σ`-integral (`norm_radialMap_of_mem`), leaving `orbitTheta K 𝔞 r · r^s`.
  have hinner : (∫ σ in normEqOneSurface K,
        Theta.idealThetaKernel K 𝔞 (radialMap K r σ) *
          (mixedEmbedding.norm (radialMap K r σ) : ℂ) ^ s ∂(surfaceMeasure K))
      = orbitTheta K 𝔞 r * (r : ℂ) ^ s := by
    rw [orbitTheta, ← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_normEqOneSurface (fun σ hσ => ?_)
    rw [norm_radialMap_of_mem r hr0 hσ]
  rw [hinner]
end DedekindZeta.ConeRadialReduction
