-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.qminor_isPol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:42:41.1568+00:00
-- url     : https://prove2.me/submissions/f5825de9-ea33-4472-befb-d267d09a469a

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_IsPol_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_IsPol_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_prod_isPol
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_Tm_lin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (a b : Fin t → Fin n) :
    IsPol (t + 1) (fun u => qminor E a b u) := by
  unfold qminor
  apply IsPol.sum
  intro σ _
  have h := (prod_isPol t (fun k => if a (σ k) = b k then (1 : A) else 0)
    (fun k => (if a (σ k) = b k then algebraMap ℂ A (-(k : ℂ)) else 0) + E (a (σ k)) (b k))).map
    (LinearMap.mulLeft ℂ (((Equiv.Perm.sign σ : ℤ) : A)))
  convert h using 2 with u
  simp only [LinearMap.mulLeft_apply, Tm_lin]
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
