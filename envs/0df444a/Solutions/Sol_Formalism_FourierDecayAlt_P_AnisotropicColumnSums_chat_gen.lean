-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AnisotropicColumnSums.chat_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:45.80192+00:00
-- url     : https://prove2.me/submissions/47fed1be-8991-4f7b-a030-e887e5c858eb

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_first_contraction_adapted


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
open Formalism.FourierDecayAlt.P.AnisotropicColumnSums
namespace Formalism.FourierDecayAlt.P.AnisotropicColumnSums
theorem _root_.solution (t n : ℕ) (h : t = n + 1) (A : Type) [Ring A] [Algebra ℂ A] (Eop : Fin t → Fin t → A)
    (P Q : Matrix (Fin t) (Fin t) ℂ) (la : Fin t) (hla : la.val = n) (ι : Fin n → Fin t)
    (hι : ∀ a, (ι a).val = a.val) (hE : GlRel Eop) (hQP : Q * P = 1) (hPQ : P * Q = 1) (u : ℂ) (β : Fin t → ℂ)
    (hβ : ∀ j, j ≠ la → (β ᵥ* P) j = 0) :
    chatA Eop u (fun p => P p la) β = (β ᵥ* P) la • qminor (Econj Eop P Q) ι ι u := by
  subst h
  have e1 : la = Fin.last n := Fin.ext hla
  subst e1
  have e2 : ι = skip1 (Fin.last n) := by
    funext a
    apply Fin.ext
    have := a.isLt
    simp [skip1, hι]
  rw [e2]
  exact first_contraction_adapted A n Eop P Q hE hQP hPQ u β hβ
end Formalism.FourierDecayAlt.P.AnisotropicColumnSums
