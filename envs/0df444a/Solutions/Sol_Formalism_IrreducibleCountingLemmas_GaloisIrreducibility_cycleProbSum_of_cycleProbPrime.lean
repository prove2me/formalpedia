-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.cycleProbSum_of_cycleProbPrime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:52.377791+00:00
-- url     : https://prove2.me/submissions/fbb6adf8-2c13-4822-8a67-2436421194a3

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRJoints

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
theorem _root_.solution : CycleProbPrime → CycleProbSum := by
  unfold CycleProbPrime CycleProbSum
  intro h N
  classical
  have hdisj : ∀ p ∈ (range (N + 1)).filter (fun p => Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N),
      ∀ q ∈ (range (N + 1)).filter (fun p => Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N), p ≠ q →
      Disjoint (univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.cycleType)
        (univ.filter fun σ : Equiv.Perm (Fin N) => q ∈ σ.cycleType) := by
    intro p hp q hq hpq
    simp only [mem_filter, mem_range] at hp hq
    rw [Finset.disjoint_left]
    intro σ h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    have hq' : q ∈ σ.cycleType.erase p := (Multiset.mem_erase_of_ne hpq.symm).2 h2
    have hsum : σ.cycleType.sum ≤ N := by
      rw [Equiv.Perm.sum_cycleType]
      exact (Finset.card_le_univ _).trans (by simp)
    have hsplit : σ.cycleType.sum = p + (σ.cycleType.erase p).sum := by
      conv_lhs => rw [← Multiset.cons_erase h1]
      rw [Multiset.sum_cons]
    have hle : q ≤ (σ.cycleType.erase p).sum := Multiset.le_sum_of_mem hq'
    omega
  have hset : (univ.filter fun σ : Equiv.Perm (Fin N) => ∃ p ∈ σ.cycleType, Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N) =
      ((range (N + 1)).filter fun p => Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N).biUnion
        (fun p => univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.cycleType) := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_range]
    constructor
    · rintro ⟨p, hp, hpr, h2, h3⟩
      exact ⟨p, ⟨by omega, hpr, h2, h3⟩, hp⟩
    · rintro ⟨p, ⟨-, hpr, h2, h3⟩, hp⟩
      exact ⟨p, hp, hpr, h2, h3⟩
  rw [hset, Finset.card_biUnion hdisj, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  simp only [mem_filter, mem_range] at hp
  obtain ⟨hpN, hpr, h2, h3⟩ := hp
  have hk := h N p hpr (by omega) h2
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpr.ne_zero
  rw [eq_div_iff hp0, ← hk]
  push_cast
  ring
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
