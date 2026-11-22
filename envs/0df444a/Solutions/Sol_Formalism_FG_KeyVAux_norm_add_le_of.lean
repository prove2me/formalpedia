-- Prove2me | solution 1 for Formalism.FG.KeyVAux.norm_add_le_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:18:13.359464+00:00
-- url     : https://prove2.me/submissions/89de8833-b982-4d84-b445-1d36bfdd136a

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Lemmata_MultivariateIntegrals_IntegralMv
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.KeyVAux
open Formalism.G Formalism.LT
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.FG.KeyVAux
theorem _root_.solution {a b : K} {C : ℝ} (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) : ‖a + b‖ ≤ C :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
end Formalism.FG.KeyVAux
