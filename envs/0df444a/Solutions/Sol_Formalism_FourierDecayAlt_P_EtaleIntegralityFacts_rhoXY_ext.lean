-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.rhoXY_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:38.651461+00:00
-- url     : https://prove2.me/submissions/4741b491-6caf-4d44-bc53-ce399be7e452

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_cofXY_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_rhoXY_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
open Formalism.FourierDecayAlt.G Matrix
noncomputable section
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
theorem _root_.solution (m : ℕ) (D t : ℂ) (p : XY m) (hc : cofXY m t p ≠ 0) (hp : ∏ k, p.1 k ≠ 0) :
    rhoXY m D t p = (-1) ^ (m + 3) * D / ∏ k, p.1 k + t * gExt m D t p := by
  have he : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; simp
  have he0 : ((-1 : ℂ) ^ m) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h0 : cof0XY m p ≠ 0 := mul_ne_zero he0 hp
  have hP : ∏ k, p.1 k = (-1) ^ m * cof0XY m p := by
    rw [cof0XY, ← mul_assoc, he, one_mul]
  have e3 : (-1 : ℂ) ^ (m + 3) = -(-1) ^ m := by rw [pow_add]; norm_num
  rw [rhoXY_eq, gExt, hP, e3]
  rw [cofXY_eq] at hc ⊢
  clear hP he e3
  generalize cof0XY m p = c0 at *
  generalize cof1XY m t p = c1 at *
  generalize r1XY m t p = r1 at *
  generalize sm m p = σ at *
  generalize ((-1 : ℂ) ^ m) = e at *
  field_simp
  ring
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
