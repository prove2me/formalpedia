-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.half_elt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:37:23.445011+00:00
-- url     : https://prove2.me/submissions/852afa50-e35d-4573-9609-4276eee07aa6

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Lemmata_FirstBlockLemmaE_Imports
import Definitions.Def_Lemmata_GeneralBFactRightTerForm_Imports
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_exists_int_quad

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
theorem _root_.solution {L : Type} [Field L] [NumberField L] (σ : Gal(L/ℚ)) (x : L) (c : ℤ)
    (hx : x ^ 2 = ((4 * c + 1 : ℤ) : L)) (hσ : σ x = -x) :
    ∃ W : 𝓞 L, W ^ 2 = W + (c : 𝓞 L) ∧ σ • W = 1 - W := by
  have hW2 : ((1 + x) / 2) ^ 2 = (1 + x) / 2 + (c : L) := by
    push_cast at hx
    linear_combination (1 / 4 : L) * hx
  obtain ⟨W, hWc, hW⟩ := exists_int_quad _ c hW2
  refine ⟨W, hW, ?_⟩
  apply RingOfIntegers.coe_injective
  show σ (W : L) = ((1 - W : 𝓞 L) : L)
  have e1 : ((1 - W : 𝓞 L) : L) = 1 - (W : L) := by push_cast; rfl
  rw [e1, hWc, map_div₀, map_add, map_one, hσ, map_ofNat]
  ring
end Formalism.TwoAdicCyclotomicDecomposition
