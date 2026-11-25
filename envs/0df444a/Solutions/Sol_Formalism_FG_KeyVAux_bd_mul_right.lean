-- Prove2me | solution 1 for Formalism.FG.KeyVAux.bd_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:33:06.332834+00:00
-- url     : https://prove2.me/submissions/a4592d7e-d7cf-44a2-bf84-18a2ee1b1cf3

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Lemmata_MultivariateIntegrals_IntegralMv
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector
import Theorems.Thm_Formalism_FG_KeyVAux_bd_mul_left

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
theorem _root_.solution {τ : Type w} {C : ℝ} (hC : 0 ≤ C) {A B : MvPowerSeries τ K}
    (hA : Bd C A) (hB : IntegralMv B) : Bd C (A * B) := by
  rw [mul_comm]; exact bd_mul_left hC hB hA
end Formalism.FG.KeyVAux
