-- Prove2me | solution 1 for Formalism.FG.KeyVAux.bd_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:33:04.176419+00:00
-- url     : https://prove2.me/submissions/fa658d02-2432-4a3f-a96a-7e1ba2644b2f

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Lemmata_MultivariateIntegrals_IntegralMv
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector
import Theorems.Thm_Formalism_FG_KeyVAux_norm_add_le_of
import Theorems.Thm_Formalism_LT_InverseIntegralClassesKeyFacts_norm_add_le_of


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
theorem _root_.solution {τ : Type w} {C : ℝ} {A B : MvPowerSeries τ K} (hA : Bd C A) (hB : Bd C B) :
    Bd C (A + B) := fun d => by rw [map_add]; exact norm_add_le_of (hA d) (hB d)
end Formalism.FG.KeyVAux
