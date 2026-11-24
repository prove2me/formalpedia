-- Prove2me | solution 1 for ChangingCache.UpperBound.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T17:05:58.093934+00:00
-- url     : https://prove2.me/submissions/5bba06e9-20be-449d-8094-18cb82fd2a4c

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_NormalForm

open ChangingCache.UpperBound

namespace Lem53Aux

variable {α : Type*} [DecidableEq α]

theorem augCap_23 (m : ℕ → ℕ) (k : ℕ) : augCap 2 3 m k = 2 * m (k / 3) := by
  unfold augCap
  rw [Nat.floor_div_ofNat, Nat.floor_natCast]

theorem lruRun_succ (C : ℕ → ℕ) (σ : List α) (k : ℕ) (hk : k < σ.length) :
    lruRun C (σ.take (k + 1)) = lruStep C (lruRun C (σ.take k)) σ[k] := by
  unfold lruRun
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.foldl_append]
  rfl

theorem lru_inv (C : ℕ → ℕ) (σ : List α) (h1 : LRUAlwaysMisses C σ) :
    ∀ k ≤ σ.length, (lruRun C (σ.take k)).misses = k ∧ (lruRun C (σ.take k)).cache.Nodup ∧
      (lruRun C (σ.take k)).cache.length = lruOccupancy C k := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [lruRun, lruOccupancy]
  | succ k ih =>
    intro hk
    have hk' : k < σ.length := by omega
    obtain ⟨hm, hnd, hlen⟩ := ih (by omega)
    have hmiss := h1 k hk'
    rw [lruRun_succ C σ k hk']
    unfold lruStep
    rw [if_neg hmiss]
    refine ⟨by simp [hm], ?_, ?_⟩
    · exact (List.nodup_cons.2 ⟨hmiss, hnd⟩).sublist (List.take_sublist _ _)
    · simp only [List.length_take, List.length_cons, hlen, hm, lruOccupancy]

theorem occ_lower (C : ℕ → ℕ) :
    ∀ k B : ℕ, B ≤ k → (∀ j, 1 ≤ j → j ≤ k → B ≤ C j + (k - j)) → B ≤ lruOccupancy C k := by
  intro k
  induction k with
  | zero =>
    intro B hB _
    omega
  | succ k ih =>
    intro B hB hj
    simp only [lruOccupancy]
    apply le_min
    · have := hj (k + 1) (by omega) le_rfl
      simpa using this
    · rcases Nat.eq_zero_or_pos B with h0 | hpos
      · omega
      · have := ih (B - 1) (by omega) (fun j hj1 hjk => by
          have := hj j hj1 (by omega)
          omega)
        omega

theorem m_le (m : ℕ → ℕ) (hm : IsMemoryProfile m) :
    ∀ q d, m (q + d) ≤ m q + d := by
  intro q d
  induction d with
  | zero => simp
  | succ d ih =>
    have := hm.2 (q + d)
    rw [← add_assoc]
    omega

end Lem53Aux

open Lem53Aux in
theorem solution {α : Type*} [DecidableEq α] (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α)
    (hred : IsReduced 2 3 m σ S) :
    ∀ i : ℕ, 1 ≤ i → 3 * i + 1 ≤ σ.length →
      (lruCache (augCap 2 3 m) σ (3 * i + 1)).card = 2 * m i ∧
        2 * m i = augCap 2 3 m (3 * i + 1) := by
  intro i hi hlen
  obtain ⟨hm, hopt, hR1, _hR2, hR3⟩ := hred
  have hdiv : (3 * i + 1) / 3 = i := by omega
  have hcap : augCap 2 3 m (3 * i + 1) = 2 * m i := by
    rw [augCap_23, hdiv]
  refine ⟨?_, hcap.symm⟩
  -- m 1 = 1 from (R3) at the first request
  have hm1 : m 1 = 1 := by
    have h0 : 0 < σ.length := by omega
    have hS0 : S 0 = ∅ := hopt.1.1
    have hmiss : missB σ S 0 = true := by
      unfold missB
      rw [List.getElem?_eq_getElem h0]
      simp [hS0]
    have := hR3 0 h0 hmiss
    simp [hS0, policyMisses] at this
    omega
  have hmi : m i ≤ i := by
    have := m_le m hm 1 (i - 1)
    rw [show 1 + (i - 1) = i by omega, hm1] at this
    omega
  obtain ⟨_, hnd, hlenc⟩ := lru_inv (augCap 2 3 m) σ hR1 (3 * i + 1) hlen
  unfold lruCache
  rw [List.toFinset_card_of_nodup hnd, hlenc]
  apply le_antisymm
  · have : lruOccupancy (augCap 2 3 m) (3 * i + 1) ≤ augCap 2 3 m (3 * i + 1) := by
      simp only [lruOccupancy]
      exact min_le_left _ _
    omega
  · apply occ_lower
    · omega
    · intro j hj1 hjk
      rw [augCap_23]
      have hq : j / 3 ≤ i := by omega
      have := m_le m hm (j / 3) (i - j / 3)
      rw [show j / 3 + (i - j / 3) = i by omega] at this
      rcases Nat.eq_or_lt_of_le hq with heq | hlt
      · rw [heq]; omega
      · have h3 : j ≤ 3 * (j / 3) + 2 := by omega
        omega
