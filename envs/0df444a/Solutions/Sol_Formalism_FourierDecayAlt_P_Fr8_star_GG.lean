-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.star_GG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:06.675325+00:00
-- url     : https://prove2.me/submissions/c4d84a5e-5e9b-4125-9b29-62936a6386b7

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_star__b_8b8b591566b9

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
namespace Formalism.FourierDecayAlt.P.Fr8
theorem _root_.solution {L : LevelData A r} (h : IsStarLevel L) : star L.GG = L.GG := by
  obtain ⟨h1, -, h3⟩ := id h
  rw [L.GG_def, star_sub, star_mul, star_ζb h, h1, ← algebraMap_star_comm, h3]
end Formalism.FourierDecayAlt.P.Fr8
