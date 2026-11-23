-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.cone_integral_idealThetaKernel_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:53:26.181477+00:00
-- url     : https://prove2.me/submissions/412a181f-bac8-4e06-a83f-ac4f7f262cd5

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_GammaIntegral_cone_integral_idealThetaKernel_eq_tsum
import Theorems.Thm_DedekindZeta_GammaIntegral_tsum_cone_integral_mixedGaussian_eq

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
open scoped nonZeroDivisors
variable {K}
namespace DedekindZeta.GammaIntegral
theorem _root_.solution (s : ℂ) (hs : 1 < s.re)
    {a : Ideal (RingOfIntegers K)} (ha : a ≠ 0) :
    ∫ x, (mixedEmbedding.fundamentalCone K).indicator
            (fun x => Theta.idealThetaKernel K a x * (mixedEmbedding.norm x : ℂ) ^ s) x
          ∂(mixedMulHaar K)
      = (Units.torsionOrder K : ℂ) * I K s *
          ∑' I : {I : (Ideal (RingOfIntegers K))⁰ //
                    (a ∣ (I : Ideal (RingOfIntegers K))) ∧
                      Submodule.IsPrincipal (I : Ideal (RingOfIntegers K))},
              (Ideal.absNorm (I : Ideal (RingOfIntegers K)) : ℂ) ^ (-s) := by
  rw [cone_integral_idealThetaKernel_eq_tsum s hs ha,
    tsum_cone_integral_mixedGaussian_eq s hs ha]
end DedekindZeta.GammaIntegral
