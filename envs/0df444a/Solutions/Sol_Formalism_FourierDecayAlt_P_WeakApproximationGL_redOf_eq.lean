-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakApproximationGL.redOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:05.600577+00:00
-- url     : https://prove2.me/submissions/3ad70bcd-5bd3-4992-9724-a5d43c206fef

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_tri_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_elim_cls

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
theorem _root_.solution (m : ℕ) (p : XY m) : redOf m p = split m (Sum.elim p.1 p.2 ∘ idx m) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact tri_lt p.1 p.2 Fin.last_pos
  · funext k
    exact tri_lt p.1 p.2 _
  · funext q
    exact (elim_cls p.1 p.2 _ _ (succ_le_castSucc q.2)).symm
  · funext i
    exact (elim_cls p.1 p.2 _ _ (Fin.le_last _)).symm
end Formalism.FourierDecayAlt.P.WeakApproximationGL
