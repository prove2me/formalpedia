-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.star_GG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:26:41.654089+00:00
-- url     : https://prove2.me/submissions/15bc706a-b0d4-49e8-a02c-fd04c30087af

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_star__b_4314c298a3a0

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
variable (L : LevelData A r)
variable {L}
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution (hS : IsStarLevel L) : star L.GG = L.GG := by
  rw [L.GG_def, star_sub, star_mul, star_ζb hS, hS.1, ← algebraMap_star_comm, hS.2.2]
end Formalism.FourierDecayAlt.P.Fr9
