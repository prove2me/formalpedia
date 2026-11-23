-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.nf21
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:36.799796+00:00
-- url     : https://prove2.me/submissions/59b35803-d6af-4edc-8a96-21ea6a04f8c0

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lA_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_diagonal_lowering_absorb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L4_xLam
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_gG
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_G

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
theorem _root_.solution {u : ℂ} (hu : Good P u) : t21 P u = t22 P u * lA P u := by
  rw [t21, t22, lA_eq, diagonal_lowering_absorb (ggA P) (ggiA P) (xA P u) _ _ (gG P) (kap_G P _), L4.xLam P hu]
end Formalism.FourierDecayAlt.P.Mx6
