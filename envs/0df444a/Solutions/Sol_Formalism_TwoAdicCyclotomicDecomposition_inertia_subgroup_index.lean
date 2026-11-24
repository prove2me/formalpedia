-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.inertia_subgroup_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:37:24.017609+00:00
-- url     : https://prove2.me/submissions/3831f47b-33d9-4ac5-a403-ae49fa604d7a

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
theorem _root_.solution (n : ℕ) : (I2 n).index = 4 := by
  rw [I2, Subgroup.index_ker, MonoidHom.range_eq_top.mpr, Subgroup.card_top, Nat.card_prod,
    Nat.card_eq_fintype_card, Fintype.card_units_int]
  intro u
  exact ⟨(1, u), rfl⟩
end Formalism.TwoAdicCyclotomicDecomposition
