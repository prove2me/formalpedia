-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliTwoByTwo.capelli_two_general_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:26.147663+00:00
-- url     : https://prove2.me/submissions/8665577c-5dcf-4e2a-a217-7c0ca320f8f5

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliTwoByTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_second_contraction_adapted


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.CapelliTwoByTwo
namespace Formalism.FourierDecayAlt.P.CapelliTwoByTwo
theorem _root_.solution (t n : ℕ) (h : t = n + 2) (A : Type) [Ring A] [Algebra ℂ A] (Eop : Fin t → Fin t → A)
    (P Q : Matrix (Fin t) (Fin t) ℂ) (i0 i1 : Fin t) (h0 : i0.val = 0) (h1 : i1.val = 1) (ι : Fin n → Fin t)
    (hι : ∀ a, (ι a).val = a.val + 2) (hE : GlRel Eop) (hQP : Q * P = 1) (hPQ : P * Q = 1) (u : ℂ) (β β' : Fin t → ℂ)
    (hβ : ∀ j : Fin t, 2 ≤ j.val → (β ᵥ* P) j = 0 ∧ (β' ᵥ* P) j = 0) :
    chat2A Eop u (fun p => P p i0) (fun p => P p i1) β β' =
      ((β ᵥ* P) i0 * (β' ᵥ* P) i1 - (β ᵥ* P) i1 * (β' ᵥ* P) i0) • qminor (Econj Eop P Q) ι ι u := by
  subst h
  have e0 : i0 = 0 := Fin.ext (by simp [h0])
  have e1 : i1 = 1 := Fin.ext (by simp [h1])
  have eι : ι = skip2 (t := n + 2) 0 1 := by
    funext a
    apply Fin.ext
    rw [hι]
    simp [skip2]
  subst e0 e1
  rw [eι]
  exact second_contraction_adapted A n Eop P Q hE hQP hPQ u β β' hβ
end Formalism.FourierDecayAlt.P.CapelliTwoByTwo
