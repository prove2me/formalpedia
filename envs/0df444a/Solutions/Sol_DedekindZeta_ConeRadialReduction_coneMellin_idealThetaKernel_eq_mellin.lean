-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.coneMellin_idealThetaKernel_eq_mellin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:49:10.171802+00:00
-- url     : https://prove2.me/submissions/48567064-8d08-4e1e-895f-f60847b40b56

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_coneMellin_idealThetaKernel_eq_radial
import Theorems.Thm_DedekindZeta_ConeRadialReduction_radialIntegral_eq_mellin

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
      = mellin (orbitTheta K 𝔞) s := by
  rw [coneMellin_idealThetaKernel_eq_radial 𝔞 s hh, radialIntegral_eq_mellin 𝔞 s]
end DedekindZeta.ConeRadialReduction
