-- Prove2me | solution 1 for DedekindZeta.ConeMellinBridge.reducedMellin_radialTheta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:45:36.253649+00:00
-- url     : https://prove2.me/submissions/7084d49b-9539-4386-a519-e13a65803db9

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Definitions.Def_DedekindZeta_ConeMellinBridge
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.ConeRadialReduction.mem_normEqOneSurface
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped Real nonZeroDivisors
open DedekindZeta DedekindZeta.ConeMellinBridge
open DedekindZeta.ConeRadialReduction DedekindZeta.MellinPrinciple
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace DedekindZeta.ConeMellinBridge
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (s : ℂ) :
    reducedMellin (radialTheta K 𝔞) (surfaceVolume K) s = mellin (orbitTheta K 𝔞) s := by
  unfold reducedMellin radialTheta
  simp
end DedekindZeta.ConeMellinBridge
