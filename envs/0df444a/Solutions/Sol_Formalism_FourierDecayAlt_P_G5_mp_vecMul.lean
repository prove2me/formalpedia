-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.mp_vecMul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:41.105915+00:00
-- url     : https://prove2.me/submissions/b0648188-131d-4e2c-828d-38d015a7f29b

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G5
theorem _root_.solution (β : ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (h : ‖M.det‖ = 1) :
    MeasurePreserving (fun x : ι → ℂ => x ᵥ* M) (muPi β ι) (muPi β ι) := by
  have := mp_mulVec β Mᵀ (by rwa [Matrix.det_transpose])
  simpa only [Matrix.mulVec_transpose] using this
end Formalism.FourierDecayAlt.P.G5
