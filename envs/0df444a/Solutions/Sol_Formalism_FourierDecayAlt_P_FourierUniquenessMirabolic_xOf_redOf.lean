-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic.xOf_redOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:27.34713+00:00
-- url     : https://prove2.me/submissions/529c7df9-8f45-4c77-a4fe-cdfe353b1d46

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_xOf_castSucc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_xOf_last


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic
theorem _root_.solution (m : ℕ) (p : XY m) (k : Fin (m + 1)) :
    xOf (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2 k = p.1 k := by
  refine Fin.lastCases ?_ (fun k => ?_) k
  · rw [G6.xOf_last]
    simp [redOf, triXY, strictUpper, Fin.succ_last]
  · rw [G6.xOf_castSucc]
    have h : k.castSucc < k.succ := Fin.castSucc_lt_succ
    simp [redOf, triXY, strictUpper, h]
end Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic
