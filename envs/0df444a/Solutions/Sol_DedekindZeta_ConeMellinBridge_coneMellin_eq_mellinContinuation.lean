-- Prove2me | solution 1 for DedekindZeta.ConeMellinBridge.coneMellin_eq_mellinContinuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:01:33.306281+00:00
-- url     : https://prove2.me/submissions/4694a054-a55b-4050-aea7-33073c4cfb1b

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Definitions.Def_DedekindZeta_ConeMellinBridge
import Theorems.Thm_DedekindZeta_ConeMellinBridge_reducedMellin_radialTheta
import Theorems.Thm_DedekindZeta_ConeMellinBridge_integrableOn_idealThetaKernel_mul_norm_cpow
import Theorems.Thm_DedekindZeta_ConeRadialReduction_coneMellin_idealThetaKernel_eq_mellin
import Theorems.Thm_DedekindZeta_ConeRadialReduction_exists_isMellinPair_radialTheta
import Theorems.Thm_DedekindZeta_MellinPrinciple_mellinContinuation_eq


set_option autoImplicit true
open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped Real nonZeroDivisors
open DedekindZeta DedekindZeta.ConeMellinBridge
open DedekindZeta.ConeRadialReduction DedekindZeta.MellinPrinciple
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace DedekindZeta.ConeMellinBridge
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) {s : ℂ}
    (hs : 1 < s.re) :
    (∫ x in mixedEmbedding.fundamentalCone K,
        Theta.idealThetaKernel K 𝔞 x * (mixedEmbedding.norm x : ℂ) ^ s
          ∂(DedekindZeta.mixedMulHaar K))
      = mellinContinuation (radialTheta K 𝔞) (radialThetaDual K 𝔞)
          (surfaceVolume K) (surfaceVolume K) ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 s := by
  obtain ⟨c, α, hpair⟩ := exists_isMellinPair_radialTheta (K := K) 𝔞 hne
  have hint := integrableOn_idealThetaKernel_mul_norm_cpow 𝔞 hs
  rw [coneMellin_idealThetaKernel_eq_mellin 𝔞 s hint,
    ← reducedMellin_radialTheta 𝔞 s,
    ← mellinContinuation_eq hpair (show ((1 : ℝ)) < s.re by exact_mod_cast hs)]
end DedekindZeta.ConeMellinBridge
