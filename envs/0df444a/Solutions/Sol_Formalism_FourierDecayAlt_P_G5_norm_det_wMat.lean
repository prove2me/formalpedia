-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.norm_det_wMat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:46:14.179561+00:00
-- url     : https://prove2.me/submissions/d898732a-69ff-4a7c-bf0f-279fbae65045

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_wMat_mul_self

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
theorem _root_.solution (d : ℕ) : ‖(wMat d).det‖ = 1 := by
  have h := congrArg (fun M => ‖Matrix.det M‖) (wMat_mul_self d)
  simp only [Matrix.det_mul, norm_mul, Matrix.det_one, norm_one] at h
  nlinarith [norm_nonneg (wMat d).det]
end Formalism.FourierDecayAlt.P.G5
