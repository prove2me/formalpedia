-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.hat_m
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:40:59.322258+00:00
-- url     : https://prove2.me/submissions/5b9abf77-0827-4643-8faa-459603498d39

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_star_d
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_di_d
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_hat_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_adjoint_l_shift_relation
import Theorems.Thm_Formalism_FourierDecayAlt_P_frame_gives_one_letter_hyps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr9
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ}
variable {L : LevelData A r} {f : FrameData S A}
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution (hS : IsStarLevel L) (h : IsFrame L f) {Y : ℂ} (hr : star Y = Y) (h1 : Y ∈ f.inv)
    (h2 : Y - 1 ∈ f.inv) : mf f.hatT (fun Y => io L.GGi * f.xi Y) Y = f.m L Y := by
  obtain ⟨H, Hl⟩ := frame_gives_one_letter_hyps A S r L f h
  have h1' : Y - 1 + 1 ∈ f.inv := by rwa [sub_add_cancel]
  have hr' : star (Y - 1) = Y - 1 := by rw [star_sub, hr, star_one]
  have adj := adjoint_l_shift_relation ℂ (SlopeTestRemainingChoices S A) f.hatT _ f.hatQ f.inv (f.d L) H (star_d hS h) (Y - 1) h2 h1'
    (hat_herm h (h.inv_reg h2) hr')
  rw [Hl _ h2 h1', sub_add_cancel] at adj
  unfold FrameData.m
  rw [mul_assoc, ← adj, ← mul_assoc, di_d h, one_mul]
end Formalism.FourierDecayAlt.P.Fr9
