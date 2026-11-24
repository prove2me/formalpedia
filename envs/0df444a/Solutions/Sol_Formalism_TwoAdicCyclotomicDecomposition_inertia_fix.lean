-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.inertia_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:49:11.38883+00:00
-- url     : https://prove2.me/submissions/aea7c055-32b8-4d35-ae58-34cde8dcc513

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Lemmata_FirstBlockLemmaE_Imports
import Definitions.Def_Lemmata_GeneralBFactRightTerForm_Imports
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_two_intCast_mem_iff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_gal_sq_fix
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_half_elt

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
theorem _root_.solution {L : Type} [Field L] [NumberField L] (x : L) (c : ℤ)
    (hx : x ^ 2 = ((4 * c + 1 : ℤ) : L))
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] (σ : Gal(L/ℚ))
    (hσ : ∀ y : 𝓞 L, σ • y - y ∈ P) : σ x = x := by
  rcases gal_sq_fix σ x _ hx with h | h
  · exact h
  exfalso
  obtain ⟨W, hW2, hσW⟩ := half_elt σ x c hx h
  have h1 : 1 - 2 * W ∈ P := by
    have := hσ W
    rw [hσW] at this
    convert this using 1
    ring
  have h2 : (1 - 2 * W) ^ 2 ∈ P := P.pow_mem_of_mem h1 2 (by norm_num)
  have h3 : (1 - 2 * W) ^ 2 = ((4 * c + 1 : ℤ) : 𝓞 L) := by
    push_cast
    linear_combination 4 * hW2
  rw [h3, two_intCast_mem_iff P] at h2
  omega
end Formalism.TwoAdicCyclotomicDecomposition
