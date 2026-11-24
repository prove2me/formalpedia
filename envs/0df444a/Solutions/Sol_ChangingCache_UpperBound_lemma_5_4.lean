-- Prove2me | solution 1 for ChangingCache.UpperBound.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T17:51:59.31687+00:00
-- url     : https://prove2.me/submissions/f504cd12-dd23-41e7-aaaf-2e7f220b0d27

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Bank

open ChangingCache.UpperBound

namespace Lem54Aux

variable {α : Type*} [DecidableEq α]

theorem lruRun_succ (C : ℕ → ℕ) (σ : List α) (k : ℕ) (hk : k < σ.length) :
    lruRun C (σ.take (k + 1)) = lruStep C (lruRun C (σ.take k)) σ[k] := by
  unfold lruRun
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.foldl_append]
  rfl

theorem lru_misses (C : ℕ → ℕ) (σ : List α) (h1 : LRUAlwaysMisses C σ) :
    ∀ k ≤ σ.length, lruMissCount C σ k = k := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [lruMissCount, lruRun]
  | succ k ih =>
    intro hk
    have hk' : k < σ.length := by omega
    have hm := ih (by omega)
    unfold lruMissCount at hm ⊢
    rw [lruRun_succ C σ k hk']
    unfold lruStep
    rw [if_neg (h1 k hk')]
    simp [hm]

theorem policyMisses_succ (σ : List α) (S : ℕ → Finset α) (k : ℕ) :
    policyMisses σ S (k + 1) = policyMisses σ S k + if missB σ S k then 1 else 0 := by
  cases h : missB σ S k <;> simp [policyMisses, List.range_succ, List.filter_append, h]

theorem policyMisses_zero (σ : List α) (S : ℕ → Finset α) : policyMisses σ S 0 = 0 := by
  simp [policyMisses]

end Lem54Aux

open Lem54Aux in
theorem solution {α : Type*} [DecidableEq α] (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α)
    (hred : IsReduced 2 3 m σ S) (hneg : ∃ r ≤ σ.length, bank3 m σ S r < 0) :
    sInf {r | r ≤ σ.length ∧ bank3 m σ S r < 0} % 3 = 1 ∧
      (∀ u < sInf {r | r ≤ σ.length ∧ bank3 m σ S r < 0}, 0 ≤ bank3 m σ S u) ∧
      ¬ Eq4At m σ S (sInf {r | r ≤ σ.length ∧ bank3 m σ S r < 0}) := by
  obtain ⟨_, _, hR1, _, _⟩ := hred
  set P : Set ℕ := {r | r ≤ σ.length ∧ bank3 m σ S r < 0} with hP
  have hne : P.Nonempty := by
    obtain ⟨r, hr, hb⟩ := hneg
    exact ⟨r, hr, hb⟩
  have hmem : sInf P ∈ P := Nat.sInf_mem hne
  set i := sInf P with hi
  obtain ⟨hilen, hib⟩ := hmem
  have hbank : ∀ r ≤ σ.length,
      bank3 m σ S r = 3 * (policyMisses σ S r : ℤ) - (r : ℤ) := by
    intro r hr
    unfold bank3
    rw [lru_misses _ σ hR1 r hr]
  have hbefore : ∀ u < i, 0 ≤ bank3 m σ S u := by
    intro u hu
    have hnot : u ∉ P := Nat.notMem_of_lt_sInf hu
    by_contra hcon
    exact hnot ⟨by omega, lt_of_not_ge hcon⟩
  refine ⟨?_, hbefore, ?_⟩
  · have hi0 : i ≠ 0 := by
      intro h0
      rw [h0, hbank 0 (Nat.zero_le _), policyMisses_zero] at hib
      simp at hib
    obtain ⟨k, hik⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [hik] at hib hilen ⊢
    have hk := hbefore k (by omega)
    rw [hbank k (by omega)] at hk
    rw [hbank (k + 1) hilen, policyMisses_succ] at hib
    split_ifs at hib <;> push_cast at hib <;> omega
  · intro h4
    unfold Eq4At at h4
    have : (0 : ℤ) ≤ (((S i).card + mu m σ S i : ℕ) : ℤ) := Int.natCast_nonneg _
    omega
