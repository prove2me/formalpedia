-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr3.c_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:25:27.492202+00:00
-- url     : https://prove2.me/submissions/71d6c5c9-6c20-41c8-8434-eb782b73fec7

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_io_mul
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_m__58fce9a2b273
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_m_b_af699ddbdd9f
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_mGGi

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
theorem _root_.solution (hf : IsFrame L f) : Commute f.c (wt L) := by
  unfold wt; rw [io_mul, io_mul]
  exact ((hf.c_fn _ (mζ L)).mul_right (hf.c_fn _ (mζb L))).mul_right (hf.c_fn _ (mGGi L))
end Formalism.FourierDecayAlt.P.Fr3
