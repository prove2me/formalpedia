-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr3.star_GG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:25:19.030052+00:00
-- url     : https://prove2.me/submissions/214ab6ee-b87a-4d19-aa4f-12457aa33219

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr3_star__b_1c4832101cb0

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
theorem _root_.solution (hL : IsStarLevel L) : star L.GG = L.GG := by
  rw [L.GG_def, star_sub, star_mul, hL.1, star_ζb hL, ← algebraMap_star_comm, hL.2.2]
end Formalism.FourierDecayAlt.P.Fr3
