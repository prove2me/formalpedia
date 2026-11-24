-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.di_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:44:15.000736+00:00
-- url     : https://prove2.me/submissions/8320a0b3-fc18-439d-9abc-f37960a15f58

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_pow_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_wti_wt

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
theorem _root_.solution (h : IsFrame L f) : f.di L * f.d L = 1 := by
  rw [Formalism.FourierDecayAlt.Fr.FrameData.di, Formalism.FourierDecayAlt.Fr.FrameData.d, mul_assoc, ← mul_assoc (Formalism.FourierDecayAlt.Fr.wti L ^ f.N),
    pow_inv (wti_wt L) f.N, one_mul, h.c_ci.2]
end Formalism.FourierDecayAlt.P.Fr8
