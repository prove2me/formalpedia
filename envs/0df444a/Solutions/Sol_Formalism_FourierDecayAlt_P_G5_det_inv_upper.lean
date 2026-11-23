-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.det_inv_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:02.235155+00:00
-- url     : https://prove2.me/submissions/73c244af-d0c5-4b94-a310-01897e17af42

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_det_upper

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
theorem _root_.solution {d : ℕ} (v : UT d → ℂ) : ((upper v)⁻¹).det = 1 := by
  rw [Matrix.det_nonsing_inv, det_upper, Ring.inverse_one]
end Formalism.FourierDecayAlt.P.G5
