-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.bruhat_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:11:46.906078+00:00
-- url     : https://prove2.me/submissions/8f542434-0c61-4cd6-9f85-20f1d1686c3f

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_bruhat_step

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
theorem _root_.solution (g : GL (Fin N) K) : ∃ u u' : GL (Fin N) K,
    IsUT (u : Matrix (Fin N) (Fin N) K) ∧ IsUT (u' : Matrix (Fin N) (Fin N) K) ∧
    ∃ (π : Equiv.Perm (Fin N)) (t : Fin N → K), (∀ j, t j ≠ 0) ∧
      ∀ i j, ((u * g * u' : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) i j =
        if i = π j then t j else 0 := by
  obtain ⟨u, u', hu, hu', p, hp⟩ := bruhat_step g N le_rfl
  refine ⟨u, u', hu, hu', ?_⟩
  set h : Matrix (Fin N) (Fin N) K := ((u * g * u' : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
  have hinj : Function.Injective p := by
    intro j j' hjj
    by_contra hne
    have h1 := (hp j j.2).2.2 j' (Ne.symm hne)
    rw [hjj] at h1
    exact (hp j' j'.2).1 h1
  refine ⟨Equiv.ofBijective p (Finite.injective_iff_bijective.mp hinj), fun j => h (p j) j,
    fun j => (hp j j.2).1, ?_⟩
  intro i j
  rw [Equiv.ofBijective_apply]
  split_ifs with hij
  · rw [hij]
  · exact (hp j j.2).2.1 i hij
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
