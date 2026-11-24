-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.frame_free_of_new_position
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:31.428524+00:00
-- url     : https://prove2.me/submissions/0cdf7603-7d2d-494e-ae45-16c8fc30952f

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2RmatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_plus_free
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_minus_free
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_start_free

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Fr.FrameFree := by
  intro A S _ _ _ _ _ _ r L st w c
  induction w with
  | nil => intro _; exact Fr4.start_free st c
  | cons l w ih =>
    intro hc
    rw [List.map_cons, List.mem_cons, not_or] at hc
    have h := ih hc.2
    show (if l.plus then (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt else (ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt).Free c
    split_ifs
    · exact Fr4.plus_free L hc.1 h l.pt
    · exact Fr4.minus_free L hc.1 h l.pt
end Formalism.FourierDecayAlt.P
