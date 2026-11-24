-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_fixed_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:59:33.957191+00:00
-- url     : https://prove2.me/submissions/b0e51a5e-c822-493f-bb96-dd28125e785d

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_two_numDerangements_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (β : Type) [Fintype β] [DecidableEq β] (hβ : 1 ≤ Fintype.card β) :
    (Fintype.card β).factorial ≤
      2 * ((univ : Finset (Equiv.Perm β)).filter (fun s => ∃ x, s x = x)).card := by
  have hd := card_derangements_eq_numDerangements β
  have h2 := two_numDerangements_le _ hβ
  have hsplit : ((univ : Finset (Equiv.Perm β)).filter (fun s => ∃ x, s x = x)).card +
      ((univ : Finset (Equiv.Perm β)).filter (fun s => ¬ ∃ x, s x = x)).card =
      (Fintype.card β).factorial := by
    rw [← Fintype.card_perm, ← Finset.card_univ]
    first
    | exact Finset.card_filter_add_card_filter_not _
    | exact Finset.filter_card_add_filter_neg_card_eq_card _
    | exact Finset.card_filter_add_card_filter_neg _
  have hneg : ((univ : Finset (Equiv.Perm β)).filter (fun s => ¬ ∃ x, s x = x)).card =
      Fintype.card (derangements β) := by
    rw [Fintype.card_subtype]
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
    exact Iff.rfl
  omega
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
