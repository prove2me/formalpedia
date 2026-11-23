-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.tri_cases
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:57:40.72113+00:00
-- url     : https://prove2.me/submissions/37fbb9f2-9646-4ae0-85cc-b035dc5bc54c

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_tri_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_tri_gt
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_tri_lt


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
theorem _root_.solution (m : ℕ) (a b : Fin (m + 2)) :
    (∀ (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ), triXY x y a b = 0) ∨
    (∃ k, ∀ (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ), triXY x y a b = x k) ∨
    (∃ e, ∀ (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ), triXY x y a b = y e) := by
  rcases lt_trichotomy a b with h | h | h
  · exact Or.inr (Or.inr ⟨⟨(a, b), h⟩, fun x y => WeakApproximationGL.tri_lt x y h⟩)
  · subst h
    induction a using Fin.cases with
    | zero => exact Or.inl fun x y => by simp [triXY, strictUpper]
    | succ k => exact Or.inr (Or.inl ⟨k, fun x y => WeakApproximationGL.tri_diag x y k⟩)
  · exact Or.inl fun x y => WeakApproximationGL.tri_gt x y h
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
