-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.N_Lams
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:16.680798+00:00
-- url     : https://prove2.me/submissions/e7bfb020-c0cd-4f07-a3a6-dde1764183a3

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_star_Lam
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_cc_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Lams_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_star_Ns
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_star_cz
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Ns_Lam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6
theorem _root_.solution (hS : NabSS) (u : ℂ) : nabA P * Lams P u = Lams P u * nabA P + cc P * Lams P u := by
  have h := congrArg star (Ns_Lam P hS (star u))
  rw [star_mul, star_sub, star_mul, star_mul, star_Lam, star_Ns, star_cz] at h
  rw [h, cc_sc, Lams_sc]; abel
end Formalism.FourierDecayAlt.P.Mx6
