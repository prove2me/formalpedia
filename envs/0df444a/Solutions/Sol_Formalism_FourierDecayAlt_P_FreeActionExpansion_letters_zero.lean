-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FreeActionExpansion.letters_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:01:30.134803+00:00
-- url     : https://prove2.me/submissions/92443181-ad73-49ee-a9c8-7024836d6a59

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionUpdateSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeActionExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FreeActionExpansion
open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
open scoped Matrix
variable {A S V : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S] [AddCommGroup V]
  [Module A V]
namespace Formalism.FourierDecayAlt.P.FreeActionExpansion
theorem _root_.solution (P Q : A[X]) (a : S) (x : Ix S → V) (hx : ∀ u, u a ≠ 0 → x u = 0) :
    ∀ L : List (Letter ℂ S), a ∉ L.map Letter.intersection_update_fsHerm_neg_one → ∀ u, u a ≠ 0 → letters P Q L x u = 0 := by
  intro L
  induction L with
  | nil => intro _ u hu; exact hx u hu
  | cons l L ih =>
    intro ha u hu
    rw [List.map_cons, List.mem_cons, not_or] at ha
    simp only [letters, placeV]
    rw [ih ha.2 _ (by rw [Function.update_of_ne ha.1]; exact hu), smul_zero]
end Formalism.FourierDecayAlt.P.FreeActionExpansion
