-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.prime_cycle_perm_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:51:01.005247+00:00
-- url     : https://prove2.me/submissions/7fd98803-3457-4a4c-81f9-481561a0e04b

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleProbPrime
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_disjoint_perm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Equiv Equiv.Perm Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (N p : ℕ) (hp : p.Prime) (hpN : p ≤ N) (hN2 : N < 2 * p)
    (S : Finset (Perm (Fin N))) (hS : ∀ σ, σ ∈ S ↔ p ∈ σ.cycleType) :
    p * S.card = N.factorial := by
  classical
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨C, hCdef⟩ : ∃ C : Finset (Perm (Fin N)), C = Finset.univ.filter (fun g => g.cycleType = {p}) :=
    ⟨_, rfl⟩
  have hmemT : ∀ σ : Perm (Fin N), p ∈ σ.cycleType ↔ ∃ c ∈ σ.cycleFactorsFinset, c.support.card = p := by
    intro σ
    rw [Equiv.Perm.cycleType_def, Multiset.mem_map]
    simp only [Finset.mem_val, Function.comp_apply]

  have hCsupp : ∀ c ∈ C, c.IsCycle ∧ c.support.card = p := by
    intro c hc
    rw [hCdef, Finset.mem_filter] at hc
    have h2 : c.support.card = p := by rw [← Equiv.Perm.sum_cycleType, hc.2, Multiset.sum_singleton]
    refine ⟨?_, h2⟩
    rw [← Equiv.Perm.card_cycleType_eq_one, hc.2, Multiset.card_singleton]
  have hmemC : ∀ c : Perm (Fin N), c.IsCycle → c.support.card = p → c ∈ C := by
    intro c hc hs
    rw [hCdef, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [hc.cycleType, hs]⟩

  have hSU : S = C.biUnion (fun c => S.filter (fun σ => c ∈ σ.cycleFactorsFinset)) := by
    ext σ
    constructor
    · intro hσ
      obtain ⟨c, hc, hcp⟩ := (hmemT σ).1 ((hS σ).1 hσ)
      exact Finset.mem_biUnion.2 ⟨c, hmemC c (Equiv.Perm.mem_cycleFactorsFinset_iff.1 hc).1 hcp,
        Finset.mem_filter.2 ⟨hσ, hc⟩⟩
    · intro h
      obtain ⟨c, _, hσ⟩ := Finset.mem_biUnion.1 h
      exact (Finset.mem_filter.1 hσ).1

  have hdisj : (C : Set (Perm (Fin N))).PairwiseDisjoint
      (fun c => S.filter (fun σ => c ∈ σ.cycleFactorsFinset)) := by
    intro c hc c' hc' hne
    show _root_.Disjoint _ _
    rw [Finset.disjoint_left]
    intro σ h1 h2
    have hd := Equiv.Perm.cycleFactorsFinset_pairwise_disjoint σ
      (Finset.mem_coe.2 (Finset.mem_filter.1 h1).2) (Finset.mem_coe.2 (Finset.mem_filter.1 h2).2) hne
    have hcard := Finset.card_le_univ (c.support ∪ c'.support)
    rw [Finset.card_union_of_disjoint hd.disjoint_support, (hCsupp c (Finset.mem_coe.1 hc)).2,
      (hCsupp c' (Finset.mem_coe.1 hc')).2, Fintype.card_fin] at hcard
    omega

  have hF : ∀ c ∈ C, (S.filter (fun σ => c ∈ σ.cycleFactorsFinset)).card = (N - p).factorial := by
    intro c hc
    obtain ⟨hcyc, hcs⟩ := hCsupp c hc
    have hB := card_disjoint_perm c (Finset.univ.filter fun τ => c.Disjoint τ) (fun τ => by simp)
    rw [Fintype.card_fin, hcs] at hB
    rw [← hB]
    symm
    refine Finset.card_bij (fun τ _ => c * τ) ?_ ?_ ?_
    · intro τ hτ
      have hd : c.Disjoint τ := (Finset.mem_filter.1 hτ).2
      have hmem : c ∈ (c * τ).cycleFactorsFinset := by
        rw [hd.cycleFactorsFinset_mul_eq_union, hcyc.cycleFactorsFinset_eq_singleton]
        exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
      exact Finset.mem_filter.2 ⟨(hS _).2 ((hmemT _).2 ⟨c, hmem, hcs⟩), hmem⟩
    · intro τ _ τ' _ h
      exact mul_left_cancel h
    · intro σ hσ
      have hmem := (Finset.mem_filter.1 hσ).2
      have hd : c.Disjoint (σ * c⁻¹) := (Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hmem).symm
      refine ⟨σ * c⁻¹, Finset.mem_filter.2 ⟨Finset.mem_univ _, hd⟩, ?_⟩
      rw [hd.commute.eq, inv_mul_cancel_right]
  have hcard : S.card = C.card * (N - p).factorial := by
    rw [hSU, Finset.card_biUnion hdisj, Finset.sum_congr rfl hF, Finset.sum_const, smul_eq_mul]
  have hC : C.card = (p - 1).factorial * N.choose p := by
    have h := Equiv.Perm.card_of_cycleType_singleton (α := Fin N) hp2 (by rw [Fintype.card_fin]; exact hpN)
    rw [Fintype.card_fin] at h
    rw [hCdef]
    exact h
  rw [hcard, hC]
  calc p * ((p - 1).factorial * N.choose p * (N - p).factorial)
      = N.choose p * (p * (p - 1).factorial) * (N - p).factorial := by ring
    _ = N.factorial := by
      rw [Nat.mul_factorial_pred hp.ne_zero, Nat.choose_mul_factorial_mul_factorial hpN]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
