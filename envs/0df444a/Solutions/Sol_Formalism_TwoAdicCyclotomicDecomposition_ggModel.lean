-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.ggModel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:22:17.469644+00:00
-- url     : https://prove2.me/submissions/7b5b1ef7-ffd8-4bb0-ac2c-0b33c8cef361

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NegOneNeOneUnitsZmodFour
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_card_GG
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_psi_inj
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_closure_le_GG
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_range_le_closure
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_range_eq_GG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : GGModel := by
  unfold GGModel
  intro s m h
  refine ⟨card_GG h, ⟨(MulEquiv.subgroupCongr (range_eq_GG h)).symm.trans
    (MonoidHom.ofInjective (psi_inj h)).symm⟩, le_antisymm ?_ (closure_le_GG h)⟩
  rw [← range_eq_GG h]
  exact range_le_closure h
end Formalism.TwoAdicCyclotomicDecomposition
