-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.frameM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:04:29.709998+00:00
-- url     : https://prove2.me/submissions/d0856112-7a97-486e-9f8a-e32cf93af45f

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_hat___ff400f1de6e6
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_hat_m
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
    (h2 : Y - 1 ∈ f.inv) : f.hatT Y 0 1 = io L.GG * f.x Y * f.m L Y := by
  obtain ⟨H, -⟩ := frame_gives_one_letter_hyps A S r L f h
  obtain ⟨-, -, -, h3, -, -⟩ := H
  rw [← hat_m hS h hr h1 h2, ← hat_τ h (h.inv_reg h1)]
  unfold mf
  rw [← mul_assoc, (h3 Y h1).1, one_mul]
end Formalism.FourierDecayAlt.P.Fr9
