-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.flip_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:19:58.677272+00:00
-- url     : https://prove2.me/submissions/7c1296f8-f7a5-417d-822a-7f8f201b9d61

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_desc_invol
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_desc_const
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_flipG_val
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {K : Type} [Field K] {N : ℕ}
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (n : GL (Fin N) K) (π : Equiv.Perm (Fin N)) (t : Fin N → K)
    (hn : ∀ i j, (n : Matrix (Fin N) (Fin N) K) i j = if i = π j then t j else 0)
    (hadm : MonoAdm π t) : flipG n = n := by
  set τ : Equiv.Perm (Fin N) := π.trans Fin.revPerm with hτ
  have hτv : ∀ i, τ i = Fin.rev (π i) := fun i => rfl
  have hlt : ∀ i j, τ j < τ i ↔ π i < π j := by
    intro i j
    rw [hτv, hτv, Fin.rev_lt_rev]
  have h1 : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → (τ i : ℕ) = τ j + 1 := by
    intro i j hij hl
    have := (hadm i j hij ((hlt i j).mp hl)).1
    rw [hτv, hτv, Fin.val_rev, Fin.val_rev]
    have := (π j).2
    omega
  have h2 : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → t i = t j := fun i j hij hl =>
    (hadm i j hij ((hlt i j).mp hl)).2
  have inv := desc_invol τ h1
  have cst := desc_const τ h1 t h2
  have hπ : ∀ x, π x = Fin.rev (τ x) := fun x => by rw [hτv, Fin.rev_rev]
  apply Units.ext
  ext i j
  rw [flipG_val, flipM_apply, hn, hn]
  by_cases hij : i = π j
  · have e1 : Fin.rev i = τ j := by rw [hij, hτv]
    rw [if_pos hij, e1, hπ (τ j), inv, if_pos rfl, cst]
  · rw [if_neg hij, if_neg]
    intro h3
    apply hij
    have e2 : j = τ (Fin.rev i) := by rw [hτv, ← h3, Fin.rev_rev]
    have e3 : τ j = Fin.rev i := by rw [e2, inv]
    rw [hπ j, e3, Fin.rev_rev]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
