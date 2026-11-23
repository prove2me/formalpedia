-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.shift_commute_relation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:24.71488+00:00
-- url     : https://prove2.me/submissions/35de3c60-883e-468c-ac47-d1a6679b494f

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_ioR_sR
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_ioR_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_r_comm

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
theorem _root_.solution : Formalism.FourierDecayAlt.M.SSComm := by
  intro P hP l hl j hj hjl
  have e1 : (kap P fun π => ((rho P π j - rho P π l - 1 : ℝ) : ℂ)) =
      ioR P (Matrix.diagonal fun π => rho P π j - rho P π l - 1) := (ioR_diag P _).symm
  have e2 : (kap P fun π => ((rho P π j - rho P π l + 1 : ℝ) : ℂ)) =
      ioR P (Matrix.diagonal fun π => rho P π j - rho P π l + 1) := (ioR_diag P _).symm
  rw [e1, e2, ← ioR_sR P l, ← ioR_sR P j]
  simp only [← map_mul]
  rw [r_comm P hP l j hl hj hjl]
end Formalism.FourierDecayAlt.P
