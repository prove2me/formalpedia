-- Prove2me | solution 1 for DedekindZeta.ConeMellinBridge.completedPartialZeta_eq_mellinContinuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:03:12.88705+00:00
-- url     : https://prove2.me/submissions/9cf2b9ab-4fec-4730-9cd6-fe14692eef81

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Definitions.Def_DedekindZeta_ConeMellinBridge
import Theorems.Thm_DedekindZeta_ConeMellinBridge_coneMellin_eq_mellinContinuation

set_option autoImplicit true
open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped Real nonZeroDivisors
open DedekindZeta DedekindZeta.ConeMellinBridge
open DedekindZeta.ConeRadialReduction DedekindZeta.MellinPrinciple
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace DedekindZeta.ConeMellinBridge
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    DedekindZeta.completedPartialZeta K 𝔞 s
      = (1 / (Units.torsionOrder K : ℂ)) * (Ideal.absNorm 𝔞 : ℂ) ^ s
          * (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2))
          * mellinContinuation (radialTheta K 𝔞) (radialThetaDual K 𝔞)
              (surfaceVolume K) (surfaceVolume K) ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 s := by
  unfold DedekindZeta.completedPartialZeta
  rw [integral_indicator (mixedEmbedding.measurableSet_fundamentalCone K),
    coneMellin_eq_mellinContinuation 𝔞 hne hs]
end DedekindZeta.ConeMellinBridge
