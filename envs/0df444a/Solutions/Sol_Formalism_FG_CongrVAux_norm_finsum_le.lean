-- Prove2me | solution 1 for Formalism.FG.CongrVAux.norm_finsum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:22.273889+00:00
-- url     : https://prove2.me/submissions/e18120ce-ceec-4ba9-83c1-68438b809339

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV

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
open Formalism Formalism.FG Formalism.FG.CongrVAux
open MvPowerSeries Formalism.G Formalism.LT Formalism.FG.SolveVAux
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}
namespace Formalism.FG.CongrVAux
theorem _root_.solution {α : Type*} {g : α → K} {C : ℝ} (hC : 0 ≤ C) (h : ∀ e, ‖g e‖ ≤ C) :
    ‖∑ᶠ e, g e‖ ≤ C := by
  by_cases hg : (Function.support g).Finite
  · rw [finsum_eq_sum g hg]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun e _ => h e
  · rw [finsum_of_infinite_support hg, norm_zero]; exact hC
end Formalism.FG.CongrVAux
