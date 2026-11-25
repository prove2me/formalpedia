-- Prove2me | solution 1 for ChromaticReconstruction.exists_equiv_of_wts_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:30:19.911925+00:00
-- url     : https://prove2.me/submissions/fee045d0-48a6-4bd6-b072-395eff51e670

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
import Theorems.Thm_ChromaticReconstruction_card_filter_weight

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K]
namespace ChromaticReconstruction
theorem _root_.solution {K' : Type*} [Fintype K'] {w : K → ℕ} {w' : K' → ℕ}
    (h : wts w = wts w') : ∃ e : K ≃ K', ∀ x, w' (e x) = w x := by
  have hfib : ∀ a, Fintype.card {x // w x = a} = Fintype.card {x' // w' x' = a} := by
    intro a
    rw [Fintype.card_subtype, Fintype.card_subtype, card_filter_weight, card_filter_weight, h]
  exact ⟨Equiv.ofFiberEquiv fun a => Fintype.equivOfCardEq (hfib a),
    Equiv.ofFiberEquiv_map _⟩
end ChromaticReconstruction
