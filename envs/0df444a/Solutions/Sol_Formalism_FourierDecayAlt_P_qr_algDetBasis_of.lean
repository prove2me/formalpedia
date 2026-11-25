-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.qr_algDetBasis_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:09:56.84882+00:00
-- url     : https://prove2.me/submissions/58887000-4f37-459b-a134-9aa0739b66f7

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_basis_iff_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_core_holds

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
theorem _root_.solution :
    Formalism.FourierDecayAlt.Qr.QJacobi → Formalism.FourierDecayAlt.Qr.DetVec → Formalism.FourierDecayAlt.Qr.MinorCov → Formalism.FourierDecayAlt.Qr.AlgDetBasis := by
  intro hJ hD hM A _ _ t E y η hE hy hη hc u p q
  exact (Formalism.FourierDecayAlt.P.ScalarCastIdentities.basis_iff_core E y η u p q).2
    (Formalism.FourierDecayAlt.P.ScalarCastIdentities.core_holds E hJ hD hM hE y η hy hη hc u p q)
end Formalism.FourierDecayAlt.P
