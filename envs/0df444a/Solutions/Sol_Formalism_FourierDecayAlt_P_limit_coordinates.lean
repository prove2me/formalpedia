-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.limit_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:48:21.225933+00:00
-- url     : https://prove2.me/submissions/78e59b1a-b0a3-40fd-869c-1f3f86971c45

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_redOf_bijective
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_xOf_redOf
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_matrix_redOf
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_strictUpper_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_diag_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.WeakApproximationGL
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.LimitCoords := by
  intro m z y
  refine ⟨redOf m (fun _ => z, y), ⟨fun k => xOf_redOf m _ k, ?_⟩, ?_⟩
  · rw [matrix_redOf, zero_smul, zero_add]
    dsimp only
    rw [diag_const]
  · rintro q ⟨hx, hM⟩
    obtain ⟨p', rfl⟩ := (redOf_bijective m).2 q
    have h1 : p'.1 = fun _ => z := funext fun k => (xOf_redOf m p' k).symm.trans (hx k)
    rw [matrix_redOf, zero_smul, zero_add, ← diag_const] at hM
    have h2 : p'.2 = y := strictUpper_injective hM
    rw [show p' = (fun _ => z, y) from Prod.ext h1 h2]
end Formalism.FourierDecayAlt.P
