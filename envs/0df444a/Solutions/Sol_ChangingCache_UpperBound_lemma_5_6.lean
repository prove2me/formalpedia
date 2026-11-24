-- Prove2me | solution 1 for ChangingCache.UpperBound.lemma_5_6
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:03:22.960857+00:00
-- url     : https://prove2.me/submissions/1db66752-0041-4f20-8a2c-4ab3c295a506

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Bank

open ChangingCache.UpperBound

namespace Lem56Aux

variable {α : Type*} [DecidableEq α]

theorem lruRun_succ (C : ℕ → ℕ) (σ : List α) (k : ℕ) (hk : k < σ.length) :
    lruRun C (σ.take (k + 1)) = lruStep C (lruRun C (σ.take k)) σ[k] := by
  unfold lruRun
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.foldl_append]
  rfl

theorem occ_le (C : ℕ → ℕ) : ∀ k, lruOccupancy C k ≤ k := by
  intro k
  induction k with
  | zero => simp [lruOccupancy]
  | succ k ih =>
    simp only [lruOccupancy]
    exact le_trans (min_le_right _ _) (by omega)

/-- Under (R1), LRU's cache after `k` requests is the reversed window of the last
`lruOccupancy C k` requests, without duplicates. -/
theorem lru_inv (C : ℕ → ℕ) (σ : List α) (h1 : LRUAlwaysMisses C σ) :
    ∀ k ≤ σ.length, (lruRun C (σ.take k)).misses = k ∧ (lruRun C (σ.take k)).cache.Nodup ∧
      (lruRun C (σ.take k)).cache.length = lruOccupancy C k ∧
      (lruRun C (σ.take k)).cache = ((σ.take k).drop (k - lruOccupancy C k)).reverse := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [lruRun, lruOccupancy]
  | succ k ih =>
    intro hk
    have hk' : k < σ.length := by omega
    obtain ⟨hm, hnd, hlen, hcache⟩ := ih (by omega)
    have hmiss := h1 k hk'
    have hck := occ_le C k
    rw [lruRun_succ C σ k hk']
    unfold lruStep
    rw [if_neg hmiss]
    refine ⟨by simp [hm], ?_, ?_, ?_⟩
    · exact (List.nodup_cons.2 ⟨hmiss, hnd⟩).sublist (List.take_sublist _ _)
    · simp only [List.length_take, List.length_cons, hlen, hm, lruOccupancy]
    · simp only [hm]
      rw [hcache]
      rw [show lruOccupancy C (k + 1) = min (C (k + 1)) (lruOccupancy C k + 1) from rfl]
      set c := lruOccupancy C k with hc
      have e1 : σ[k] :: ((σ.take k).drop (k - c)).reverse =
          ((σ.take k).drop (k - c) ++ [σ[k]]).reverse := by simp
      have e2 : (σ.take k).drop (k - c) ++ [σ[k]] = (σ.take (k + 1)).drop (k - c) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk',
          List.drop_append_of_le_length (by rw [List.length_take]; omega)]
        rfl
      have hL : ((σ.take (k + 1)).drop (k - c)).length = c + 1 := by
        rw [List.length_drop, List.length_take]; omega
      rw [e1, e2, List.take_reverse, List.drop_drop, hL]
      rw [show k - c + (c + 1 - C (k + 1)) = k + 1 - min (C (k + 1)) (c + 1) by omega]

theorem policyMisses_succ (σ : List α) (S : ℕ → Finset α) (k : ℕ) :
    policyMisses σ S (k + 1) = policyMisses σ S k + if missB σ S k then 1 else 0 := by
  cases h : missB σ S k <;> simp [policyMisses, List.range_succ, List.filter_append, h]

/-- Every page a legal policy holds at `t`, or that is requested in `[u, t)`, was already held at
`u` or was loaded at one of the policy's misses in `[u, t)`; the loaded pages number at most the
misses in that window. -/
theorem held_or_loaded (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α) (hS : IsLegal m σ S)
    (u : ℕ) : ∀ t, u ≤ t → t ≤ σ.length →
      ∃ L : Finset α, L.card + policyMisses σ S u ≤ policyMisses σ S t ∧
        S t ⊆ S u ∪ L ∧
        ∀ s, u ≤ s → s < t → ∀ x ∈ σ[s]?, x ∈ S u ∪ L := by
  intro t hut
  induction t, hut using Nat.le_induction with
  | base =>
    intro _
    refine ⟨∅, by simp, by simp, ?_⟩
    intro s h1 h2
    omega
  | succ t hut ih =>
    intro ht
    have ht' : t < σ.length := by omega
    obtain ⟨L, hcard, hsub, hreq⟩ := ih (by omega)
    have hstep := (hS.2 t ht').1
    by_cases hmiss : σ[t] ∈ S t
    · have hmB : missB σ S t = false := by
        unfold missB
        rw [List.getElem?_eq_getElem ht']
        simp [hmiss]
      refine ⟨L, ?_, ?_, ?_⟩
      · rw [policyMisses_succ, hmB]; simpa using hcard
      · intro x hx
        have := hstep hx
        rw [Finset.mem_insert] at this
        rcases this with h | h
        · exact hsub (h ▸ hmiss)
        · exact hsub h
      · intro s h1 h2 x hx
        rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h | h
        · exact hreq s h1 h x hx
        · subst h
          rw [List.getElem?_eq_getElem ht', Option.mem_def, Option.some.injEq] at hx
          subst hx
          exact hsub hmiss
    · have hmB : missB σ S t = true := by
        unfold missB
        rw [List.getElem?_eq_getElem ht']
        simp [hmiss]
      refine ⟨insert σ[t] L, ?_, ?_, ?_⟩
      · rw [policyMisses_succ, hmB]
        have := Finset.card_insert_le σ[t] L
        simp only [if_true]
        omega
      · intro x hx
        have := hstep hx
        rw [Finset.mem_insert] at this
        rcases this with h | h
        · rw [h]; simp
        · have := hsub h
          rw [Finset.mem_union] at this ⊢
          rcases this with h' | h'
          · exact Or.inl h'
          · exact Or.inr (Finset.mem_insert_of_mem h')
      · intro s h1 h2 x hx
        rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h | h
        · have := hreq s h1 h x hx
          rw [Finset.mem_union] at this ⊢
          rcases this with h' | h'
          · exact Or.inl h'
          · exact Or.inr (Finset.mem_insert_of_mem h')
        · subst h
          rw [List.getElem?_eq_getElem ht', Option.mem_def, Option.some.injEq] at hx
          subst hx
          simp

end Lem56Aux

open Lem56Aux in
theorem solution {α : Type*} [DecidableEq α] (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α)
    (hred : IsReduced 2 3 m σ S) :
    ∀ i ≤ σ.length, ∀ u, u + (lruCache (augCap 2 3 m) σ i).card ≤ i →
      (lruCache (augCap 2 3 m) σ i).card + mu m σ S i + policyMisses σ S u ≤
        (S u).card + policyMisses σ S i := by
  obtain ⟨_, hopt, hR1, _, _⟩ := hred
  intro i hi u hu
  set C := augCap 2 3 m with hC
  obtain ⟨_, hnd, hlen, hcache⟩ := lru_inv C σ hR1 i hi
  have hcard : (lruCache C σ i).card = lruOccupancy C i := by
    unfold lruCache
    rw [List.toFinset_card_of_nodup hnd, hlen]
  obtain ⟨L, hLcard, hSsub, hreq⟩ := held_or_loaded m σ S hopt.1 u i (by omega) hi
  have hsub : S i ∪ lruCache C σ i ⊆ S u ∪ L := by
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact hSsub hx
    · unfold lruCache at hx
      rw [hcache, List.toFinset_reverse, List.mem_toFinset, List.mem_drop_iff_getElem] at hx
      obtain ⟨j, hj, hjx⟩ := hx
      rw [List.length_take] at hj
      rw [List.getElem_take] at hjx
      have hc := hcard
      refine hreq (i - lruOccupancy C i + j) (by omega) (by omega) x ?_
      rw [List.getElem?_eq_getElem (by omega), Option.mem_def, hjx]
  have h1 : (S i \ lruCache C σ i).card + (lruCache C σ i).card ≤ (S u).card + L.card := by
    rw [Finset.card_sdiff_add_card]
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  unfold mu
  rw [← hC]
  omega
