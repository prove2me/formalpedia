-- Prove2me | solution 1 for Formalism.FG.KeyVAux.norm_finsum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:58.470936+00:00
-- url     : https://prove2.me/submissions/5d7883c6-17d6-40f7-88f7-878b21ba5c94

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
theorem _root_.solution {α : Type v} {g : α → K} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) :
    ‖∑ᶠ n, g n‖ ≤ C := by
  classical
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum g hfin]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => hg i)
  · rw [finsum_of_infinite_support hfin]
    simpa using hC
end Formalism.FG.KeyVAux
