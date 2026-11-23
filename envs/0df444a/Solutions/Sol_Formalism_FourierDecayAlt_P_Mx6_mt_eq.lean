-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.mt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:47.078779+00:00
-- url     : https://prove2.me/submissions/581d413a-c1b2-4ea6-8b1e-df2954249fb4

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lA_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_star_Lam
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lowering_constant_eq_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Lams_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_G_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_star_G
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_star_N
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_star_cc

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
theorem _root_.solution (u : ℂ) : mt P u = -nabsA P - (u + 1 / 2) • cz P + ggiA P * Lams P u := by
  unfold mt
  rw [lA_eq, lowering_constant_eq_shift, star_add, star_sub, star_neg, star_N, star_smul, star_cc, star_mul, star_Lam, star_G, G_sc, Lams_sc]
  congr 3
  simp
end Formalism.FourierDecayAlt.P.Mx6
