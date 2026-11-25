-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.eigenvalue_interlacing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:11:57.721298+00:00
-- url     : https://prove2.me/submissions/0fe514c9-039d-42f0-8d94-083b2f88fda2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RhoAntitoneOfInterlacing
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivedCoefficientIntegrable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EigenvalueInterlacing
import Theorems.Thm_Formalism_FourierDecayAlt_P_interlacing_of_parts
import Theorems.Thm_Formalism_FourierDecayAlt_P_le_E_proof
import Theorems.Thm_Formalism_FourierDecayAlt_P_roots_outside_jointly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.C7.LemmaEInterlacing :=
  interlacing_of_parts le_E_proof roots_outside_jointly
end Formalism.FourierDecayAlt.P
