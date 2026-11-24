-- Prove2me | solution 1 for ChangingCache.UpperBound.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T17:25:18.173837+00:00
-- url     : https://prove2.me/submissions/287d7fed-752e-445c-ba42-519974bbafe3

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_NormalForm

open ChangingCache.UpperBound

namespace Lem52Aux

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

theorem occ_succ_le (C : ℕ → ℕ) (k : ℕ) : lruOccupancy C (k + 1) ≤ lruOccupancy C k + 1 := by
  simp only [lruOccupancy]
  exact min_le_right _ _

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

theorem occ_mono (C : ℕ → ℕ) (i j : ℕ) (hij : i ≤ j) :
    (i : ℤ) - (lruOccupancy C i : ℤ) ≤ (j : ℤ) - (lruOccupancy C j : ℤ) := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    have := occ_succ_le C j
    push_cast
    omega

end Lem52Aux

open Lem52Aux in
theorem solution {α : Type*} [DecidableEq α] (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α)
    (hred : IsReduced 2 3 m σ S) :
    (∀ i ≤ σ.length,
      (lruCache (augCap 2 3 m) σ i).card ≤ i ∧
      ((σ.take i).drop (i - (lruCache (augCap 2 3 m) σ i).card)).Nodup ∧
      lruCache (augCap 2 3 m) σ i =
        ((σ.take i).drop (i - (lruCache (augCap 2 3 m) σ i).card)).toFinset) ∧
    (∀ i j, i ≤ j → j ≤ σ.length →
      (i : ℤ) - ((lruCache (augCap 2 3 m) σ i).card : ℤ) ≤
        (j : ℤ) - ((lruCache (augCap 2 3 m) σ j).card : ℤ)) ∧
    (∀ i ≤ σ.length, ∀ i', 1 ≤ i' → i' ≤ i →
      (i : ℤ) - ((lruCache (augCap 2 3 m) σ i).card : ℤ) < (i' : ℤ) →
      ∀ u, i' ≤ u → u ≤ i → ∀ p ∈ σ[i' - 1]?, p ∈ lruCache (augCap 2 3 m) σ u) := by
  obtain ⟨_, _, hR1, _, _⟩ := hred
  set C := augCap 2 3 m with hC
  have hcard : ∀ i ≤ σ.length, (lruCache C σ i).card = lruOccupancy C i := by
    intro i hi
    obtain ⟨_, hnd, hlen, _⟩ := lru_inv C σ hR1 i hi
    unfold lruCache
    rw [List.toFinset_card_of_nodup hnd, hlen]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨_, hnd, _, hcache⟩ := lru_inv C σ hR1 i hi
    rw [hcard i hi]
    refine ⟨occ_le C i, ?_, ?_⟩
    · rw [hcache] at hnd
      exact List.nodup_reverse.1 hnd
    · unfold lruCache
      rw [hcache, List.toFinset_reverse]
  · intro i j hij hj
    rw [hcard i (le_trans hij hj), hcard j hj]
    exact occ_mono C i j hij
  · intro i hi i' hi'1 hi'i hlt u hiu hui p hp
    have hu : u ≤ σ.length := le_trans hui hi
    rw [hcard i hi] at hlt
    have hmono := occ_mono C u i hui
    have hou := occ_le C u
    have hlow : u - lruOccupancy C u ≤ i' - 1 := by omega
    have hx : i' - 1 < σ.length := by omega
    rw [List.getElem?_eq_getElem hx, Option.mem_def, Option.some.injEq] at hp
    subst hp
    obtain ⟨_, _, _, hcache⟩ := lru_inv C σ hR1 u hu
    unfold lruCache
    rw [hcache, List.toFinset_reverse, List.mem_toFinset, List.mem_drop_iff_getElem]
    refine ⟨i' - 1 - (u - lruOccupancy C u), ?_, ?_⟩
    · rw [List.length_take]; omega
    · rw [List.getElem_take]
      congr 1
      omega
