-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_stab_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:59:34.848448+00:00
-- url     : https://prove2.me/submissions/a9172f16-436e-4c21-baad-cab2bf86f45c

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_stab_iff

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
variable {N : ℕ}
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (A : Finset (Fin N)) :
    ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => ∀ x ∈ A, σ x ∈ A)).card ≤
      A.card.factorial * (N - A.card).factorial := by
  have key : Fintype.card {σ : Equiv.Perm (Fin N) // ∀ x ∈ A, σ x ∈ A} ≤
      Fintype.card (Equiv.Perm {x // x ∈ A} × Equiv.Perm {x // x ∉ A}) := by
    refine Fintype.card_le_of_injective
      (fun σ => (σ.1.subtypePerm (fun x => stab_iff A σ.1 σ.2 x),
        σ.1.subtypePerm (fun x => not_congr (stab_iff A σ.1 σ.2 x)))) ?_
    rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ he
    simp only [Prod.mk.injEq] at he
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ A
    · have := congrArg (fun e => (e ⟨x, hx⟩ : Fin N)) he.1
      exact congrArg Fin.val (by simpa using this)
    · have := congrArg (fun e => (e ⟨x, hx⟩ : Fin N)) he.2
      exact congrArg Fin.val (by simpa using this)
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_perm, Fintype.card_coe,
    Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe] at key
  calc _ = Fintype.card {σ : Equiv.Perm (Fin N) // ∀ x ∈ A, σ x ∈ A} := (Fintype.card_subtype _).symm
    _ ≤ _ := key
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
