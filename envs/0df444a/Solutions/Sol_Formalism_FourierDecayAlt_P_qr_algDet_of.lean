-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.qr_algDet_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:11:57.126967+00:00
-- url     : https://prove2.me/submissions/0ddd5435-9bf9-4d7d-aa59-33ecba447519

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_basis_iff_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_algDet_of_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Qr.AlgDetBasis → Formalism.FourierDecayAlt.Qr.AlgDet := by
  intro h A _ _ t E y η hE hy hη hc u x ξ
  exact Formalism.FourierDecayAlt.P.ScalarCastIdentities.algDet_of_core E y η u
    (fun p q => (Formalism.FourierDecayAlt.P.ScalarCastIdentities.basis_iff_core E y η u p q).1 (h A t E y η hE hy hη hc u p q)) x ξ
end Formalism.FourierDecayAlt.P
