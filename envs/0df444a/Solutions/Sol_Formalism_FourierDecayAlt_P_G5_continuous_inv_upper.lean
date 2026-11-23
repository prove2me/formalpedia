-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.continuous_inv_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:01.969535+00:00
-- url     : https://prove2.me/submissions/e051174e-9a64-4414-ada2-4d4c67a5432f

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_det_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_continuous_upper

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
theorem _root_.solution (d : ℕ) : Continuous (fun v : UT d → ℂ => (upper v)⁻¹) := by
  have h : (fun v : UT d → ℂ => (upper v)⁻¹) = fun v => (upper v).adjugate := by
    funext v
    rw [Matrix.inv_def, det_upper, Ring.inverse_one, one_smul]
  rw [h]
  exact (continuous_upper d).matrix_adjugate
end Formalism.FourierDecayAlt.P.G5
