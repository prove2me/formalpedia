-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.range_eq_GG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:50.143829+00:00
-- url     : https://prove2.me/submissions/7144a54a-7c19-47c3-8afb-a85922f959ba

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NegOneNeOneUnitsZmodFour
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_card_GG
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_psi_inj
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_card_dom
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_closure_le_GG
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_range_le_closure

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
theorem _root_.solution {s m : ℕ} (h : s ≤ m) : (psi h).range = GG h := by
  apply Subgroup.eq_of_le_of_card_ge ((range_le_closure h).trans (closure_le_GG h))
  exact le_of_eq (by rw [card_GG h, ← Nat.card_congr (MonoidHom.ofInjective (psi_inj h)).toEquiv, card_dom])
end Formalism.TwoAdicCyclotomicDecomposition
