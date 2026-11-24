-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.star_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:21:00.331801+00:00
-- url     : https://prove2.me/submissions/c74a90b8-7616-4055-a10a-ede60eee850b

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_star_wt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_c_wt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr8
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
variable {L : LevelData A r} {f : FrameData S A}
namespace Formalism.FourierDecayAlt.P.Fr8
theorem _root_.solution (hS : IsStarLevel L) (h : IsFrame L f) : star (f.d L) = f.d L := by
  rw [Formalism.FourierDecayAlt.Fr.FrameData.d, star_mul, star_pow, star_wt hS, h.c_star]
  exact (c_wt h).pow_right f.N
end Formalism.FourierDecayAlt.P.Fr8
