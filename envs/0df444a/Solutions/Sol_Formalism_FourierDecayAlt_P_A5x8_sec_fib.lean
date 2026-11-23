-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.sec_fib
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:06.311667+00:00
-- url     : https://prove2.me/submissions/64573646-fa54-4ca2-8114-a4159c7e28a1

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution {A X G QA QX QG : Type} (cA : A → QA) (oA : QA → A) (hA : ∀ q, cA (oA q) = q)
    (cX : X → QX) (oX : QX → X) (hX : ∀ q, cX (oX q) = q) (cG : G → QG)
    (hG : Function.Surjective cG) (J : A → X → G) (S : ∀ g, ∃ a x, g = J a x)
    (E1 : ∀ a x a' x', cG (J a x) = cG (J a' x') → cA a = cA a')
    (E2 : ∀ a x x', cG (J a x) = cG (J a x') ↔ cX x = cX x')
    (E3 : ∀ a a', cA a = cA a' → ∀ x, ∃ x', cG (J a x) = cG (J a' x')) :
    Function.Bijective (fun p : QA × QX => cG (J (oA p.1) (oX p.2))) := by
  constructor
  · rintro ⟨p, q⟩ ⟨p', q'⟩ h
    simp only at h
    have h1 := E1 _ _ _ _ h
    rw [hA, hA] at h1
    subst h1
    have h2 := (E2 _ _ _).1 h
    rw [hX, hX] at h2
    rw [h2]
  · intro g'
    obtain ⟨g, rfl⟩ := hG g'
    obtain ⟨a, x, rfl⟩ := S g
    obtain ⟨x', hx'⟩ := E3 a (oA (cA a)) (hA _).symm x
    refine ⟨(cA a, cX x'), ?_⟩
    simp only
    rw [hx']
    exact (E2 _ _ _).2 (hX _)
end Formalism.FourierDecayAlt.P.A5x8
