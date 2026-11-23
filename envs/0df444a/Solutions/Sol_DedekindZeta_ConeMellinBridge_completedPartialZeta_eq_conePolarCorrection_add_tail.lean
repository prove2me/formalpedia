-- Prove2me | solution 1 for DedekindZeta.ConeMellinBridge.completedPartialZeta_eq_conePolarCorrection_add_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:05:47.626022+00:00
-- url     : https://prove2.me/submissions/077fd565-8726-4de1-86ec-ff680faafd1d

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Definitions.Def_DedekindZeta_ConeMellinBridge
import Theorems.Thm_DedekindZeta_ConeMellinBridge_mellinContinuation_eq_conePolarCorrection_add_tail
import Theorems.Thm_DedekindZeta_ConeMellinBridge_completedPartialZeta_eq_mellinContinuation

set_option autoImplicit true
open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped Real nonZeroDivisors
open DedekindZeta DedekindZeta.ConeMellinBridge
open DedekindZeta.ConeRadialReduction DedekindZeta.MellinPrinciple
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (K)
variable {K}
namespace DedekindZeta.ConeMellinBridge
theorem _root_.solution (𝔞 : Ideal (𝓞 K))
    (hne : 𝔞 ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    DedekindZeta.completedPartialZeta K 𝔞 s
      = (1 / (Units.torsionOrder K : ℂ)) * (Ideal.absNorm 𝔞 : ℂ) ^ s
          * (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2))
          * (conePolarCorrection K 𝔞 s
              + mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
                  (surfaceVolume K) (surfaceVolume K) ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 s) := by
  rw [completedPartialZeta_eq_mellinContinuation 𝔞 hne hs,
    mellinContinuation_eq_conePolarCorrection_add_tail]
end DedekindZeta.ConeMellinBridge
