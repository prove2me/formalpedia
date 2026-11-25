-- Prove2me | solution 1 for Formalism.IncomingBounds.tpjet_jetAt0_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:58:26.485855+00:00
-- url     : https://prove2.me/submissions/61d67244-8427-45d6-aed8-9686beaf8558

import Definitions.Def_Formalism_IncomingBounds_DefsThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPJet
import Theorems.Thm_Formalism_IncomingBounds_tpjet_jetAt0_add
import Theorems.Thm_Formalism_IncomingBounds_tpjet_jetAt0_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
variable {C : Type} [Field C]
namespace Formalism.IncomingBounds
theorem _root_.solution {σ ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ C)
    (G : MvPowerSeries σ C) : jetAt0 (∑ j ∈ s, P j) G = ∑ j ∈ s, jetAt0 (P j) G := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, tpjet_jetAt0_zero]
  · intro j t hj ih
    rw [Finset.sum_insert hj, Finset.sum_insert hj, tpjet_jetAt0_add, ih]
end Formalism.IncomingBounds
