-- Prove2me | solution 1 for CommitteeVoting.SingleVoter.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:14:56.631983+00:00
-- url     : https://prove2.me/submissions/482abeda-1810-49a8-bf8a-74b9ffa4c10d

import Mathlib
import Definitions.Def_CommitteeVoting_SingleVoter_PoissonBinomial
set_option autoImplicit false
open CommitteeVoting.SingleVoter

theorem solution {n : ℕ} (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (ℓ : ℕ) (hℓ : ℓ ≤ n) :
    pbPMF p Finset.univ ℓ = pbPMF (p ∘ σ) Finset.univ ℓ := by
  unfold pbPMF
  refine Finset.sum_nbij' (fun A => A.map σ.symm.toEmbedding) (fun A => A.map σ.toEmbedding)
    ?_ ?_ ?_ ?_ ?_
  · intro A hA
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hA ⊢
    simpa using hA
  · intro A hA
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hA ⊢
    simpa using hA
  · intro A _
    ext x; simp
  · intro A _
    ext x; simp
  · intro A _
    unfold pbWeight
    have h2 : Finset.univ \ A.map σ.symm.toEmbedding = (Finset.univ \ A).map σ.symm.toEmbedding := by
      ext x; simp
    simp only [Function.comp]
    rw [h2, Finset.prod_map, Finset.prod_map]
    simp
