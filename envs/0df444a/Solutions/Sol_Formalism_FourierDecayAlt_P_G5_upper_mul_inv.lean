-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.upper_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:20.784873+00:00
-- url     : https://prove2.me/submissions/d7f1f597-0690-4186-b3b2-0e96ddfc6042

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
theorem _root_.solution {d : ℕ} (v : UT d → ℂ) : upper v * (upper v)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (by rw [det_upper]; exact isUnit_one)
end Formalism.FourierDecayAlt.P.G5
