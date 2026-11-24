-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.decomposition_subgroup_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:37:21.224289+00:00
-- url     : https://prove2.me/submissions/f14ae289-4a8f-4576-93ef-ca034c744d48

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Lemmata_FirstBlockLemmaE_Imports
import Definitions.Def_Lemmata_GeneralBFactRightTerForm_Imports
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution (n : ℕ) : (D2 n).index = 2 := by
  rw [D2, Subgroup.index_ker, MonoidHom.range_eq_top.mpr, Subgroup.card_top,
    Nat.card_eq_fintype_card, Fintype.card_units_int]
  intro u
  exact ⟨(1, 1, u), rfl⟩
end Formalism.TwoAdicCyclotomicDecomposition
