-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakApproximationGL.elim_cls
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:51.150589+00:00
-- url     : https://prove2.me/submissions/105ad9f3-ddf9-468b-9c71-e06e5186a047

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_tri_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_tri_lt

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
theorem _root_.solution {m : ℕ} (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) (i : Fin (m + 1)) (j : Fin (m + 2))
    (h : i.succ ≤ j) : Sum.elim x y (cls i j h) = triXY x y i.succ j := by
  unfold cls
  split_ifs with h'
  · subst h'
    exact (tri_diag x y i).symm
  · exact (tri_lt x y _).symm
end Formalism.FourierDecayAlt.P.WeakApproximationGL
