-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr3.commute_x_l0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:25:28.418111+00:00
-- url     : https://prove2.me/submissions/5c2eab0f-cbcd-4a5c-89a5-70e5d0f72762

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_io_mul
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_m_b_af699ddbdd9f
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_mGGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_io_alg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr3
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ} {L : LevelData A r} {f : FrameData S A}
namespace Formalism.FourierDecayAlt.P.Fr3
theorem _root_.solution (hf : IsFrame L f) (Ya Y : ℂ) : Commute (f.x Ya) (io (L.l0 Y)) := by
  unfold LevelData.l0
  have e : (io (-L.nab - algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) : SlopeTestRemainingChoices S A) =
      -io L.nab - algebraMap ℂ (SlopeTestRemainingChoices S A) (Y + 1 / 2) * (io L.ζb * io L.GGi) := by
    rw [← io_alg, ← io_mul, ← io_mul]; simp only [io, map_sub, map_neg]
  rw [e]
  exact ((hf.x_nab Ya).neg_right).sub_right ((Algebra.commute_algebraMap_right _ _).mul_right
    ((hf.x_fn Ya _ (mζb L)).mul_right (hf.x_fn Ya _ (mGGi L))))
end Formalism.FourierDecayAlt.P.Fr3
