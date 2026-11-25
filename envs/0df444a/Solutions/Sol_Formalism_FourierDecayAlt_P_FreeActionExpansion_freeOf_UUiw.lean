-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FreeActionExpansion.freeOf_UUiw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:18:48.560489+00:00
-- url     : https://prove2.me/submissions/2adb203d-4645-4841-8b5f-eeb44a334cdf

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionUpdateSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeActionExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FreeActionExpansion_freeOf_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_CoordinateFlipUpdateSums_freeOf_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_CoordinateFlipUpdateSums_freeOf_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_free
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_ins_free
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_ins_free


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
variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.FreeActionExpansion
theorem _root_.solution (a : S) (s : ℂ) : ∀ L : List (Letter ℂ S),
    a ∉ L.map Letter.intersection_update_fsHerm_neg_one → FreeOf a (UUiw s L : SlopeTestRemainingChoices S A) := by
  intro L
  induction L with
  | nil => intro _; exact freeOf_one a
  | cons l L ih =>
    intro ha
    rw [List.map_cons, List.mem_cons, not_or] at ha
    simp only [UUiw]
    exact freeOf_mul (Formalism.FourierDecayAlt.P.Wd1.ins_free ha.1 _ fun i j => freeOf_io a _) (ih ha.2)
end Formalism.FourierDecayAlt.P.FreeActionExpansion
