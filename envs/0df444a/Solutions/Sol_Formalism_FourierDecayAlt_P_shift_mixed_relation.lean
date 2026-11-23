-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.shift_mixed_relation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:39.256542+00:00
-- url     : https://prove2.me/submissions/57be5138-619f-4da3-a8a2-5357d5bc2c22

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_ioR_sR
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_ioR_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_r_mixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Mx4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.SSMixed := by
  intro P hP l hl j hj hjl
  rw [← ioR_sR P l, ← ioR_sR P j, ← ioR_transpose]
  simp only [← map_mul]
  rw [r_mixed P hP l j hl hj hjl]
end Formalism.FourierDecayAlt.P
