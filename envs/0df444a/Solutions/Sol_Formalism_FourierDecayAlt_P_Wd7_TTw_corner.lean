-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.TTw_corner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:24:59.437549+00:00
-- url     : https://prove2.me/submissions/e69c17f7-bebe-404b-8924-80231fa5bb79

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_mul_io_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_TTw_factor
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_mul_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_Xp_fix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_Xm_fix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution (QQ : K → M2 A) (w : List (Letter K S)) (Y : K)
    (hn : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) (hr : Reg w Y) (z : Ix S) :
    (TTw QQ w Y 0 0) z e1 = if z = e1 then QQ Y 0 0 else 0 := by
  rw [TTw_factor, mul_col _ _ (Xp_fix w Y hr), Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Matrix.add_apply, lift0, Matrix.map_apply, mul_io_apply, Xm_fix w Y hn hr]
  by_cases hz : z = e1 <;> simp [hz]
end Formalism.FourierDecayAlt.P.Wd7
