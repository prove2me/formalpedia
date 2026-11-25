-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.assemble_least_norm_and_sizes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:35:04.541262+00:00
-- url     : https://prove2.me/submissions/334364a5-d25d-40b7-9b23-8a07b0826697

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_leastNorm
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_sizeQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S6.AssembleLeast :=
  fun h1 hW hD hdeg h2 h3 hN =>
    ⟨leastNorm h1 hW h2 h3 hN, sizeQuotient (leastNorm h1 hW h2 h3 hN) hD hdeg⟩
end Formalism.FourierDecayAlt.P
