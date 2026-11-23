-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakApproximationGL.xOf_redOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:27.643583+00:00
-- url     : https://prove2.me/submissions/3b3e0f0b-f3d1-4c5b-acf1-ade74fffac82

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_tri_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_cl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakApproximationGL
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G5
namespace Formalism.FourierDecayAlt.P.WeakApproximationGL
theorem _root_.solution (m : ℕ) (p : XY m) (k : Fin (m + 1)) :
    xOf (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2 k = p.1 k := by
  induction k using Fin.lastCases with
  | last =>
    simp only [xOf, Fin.succ_last, blk_cl]
    exact tri_diag p.1 p.2 (Fin.last m)
  | cast c =>
    simp only [xOf, Fin.succ_castSucc, blk_cc, strictUpper, Matrix.of_apply,
      dif_pos (Fin.castSucc_lt_succ (i := c))]
    exact tri_diag p.1 p.2 c.castSucc
end Formalism.FourierDecayAlt.P.WeakApproximationGL
