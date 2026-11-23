-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.transfer_rtt_entries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:00.798139+00:00
-- url     : https://prove2.me/submissions/dd954c45-9394-4afd-8dd2-505157d7fe32

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_entries_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_m_curvature_proof
import Theorems.Thm_Formalism_FourierDecayAlt_P_nabla_shift_relation
import Theorems.Thm_Formalism_FourierDecayAlt_P_shift_commute_relation
import Theorems.Thm_Formalism_FourierDecayAlt_P_shift_mixed_relation
import Theorems.Thm_Formalism_FourierDecayAlt_P_shift_norm_relation


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.QQRTTEntries :=
  Mx6.entries_of shift_norm_relation shift_commute_relation shift_mixed_relation nabla_shift_relation m_curvature_proof
end Formalism.FourierDecayAlt.P
