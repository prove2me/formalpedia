-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.shift_norm_relation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:49.876527+00:00
-- url     : https://prove2.me/submissions/0b4db477-3157-4249-b87b-539629ba112b

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_ioR_sR
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_ioR_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_ioR_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_r_norm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_r_normDown

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
theorem _root_.solution : Formalism.FourierDecayAlt.M.SSNorm := by
  intro P hP l hl
  constructor
  · rw [← ioR_sR P l, ← ioR_transpose, ← map_mul, r_norm P hP l hl, ioR_diag]
  · rw [← ioR_sR P l, ← ioR_transpose, ← map_mul, r_normDown P hP l hl, ioR_diag]
end Formalism.FourierDecayAlt.P
