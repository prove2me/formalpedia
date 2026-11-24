-- Prove2me | solution 1 for ChangingCache.UpperBound.lemma_5_5
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:22:26.163298+00:00
-- url     : https://prove2.me/submissions/a20e7382-d6e6-4cdb-bf78-177464d37423

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_Bank

open ChangingCache.UpperBound

namespace Lem55Aux

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

/-- Equation (4) holds at every position `≡ 1 (mod 3)` in `[1, n]` before its first failure, and
the first failure is at most `n + 1`. -/
theorem eq4_before (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α) :
    eq4FirstFailure m σ S ≤ σ.length + 1 ∧
    ∀ p, p < eq4FirstFailure m σ S → 1 ≤ p → p ≤ σ.length → p % 3 = 1 → Eq4At m σ S p := by
  classical
  unfold eq4FirstFailure
  split_ifs with h
  · refine ⟨?_, ?_⟩
    · have := Nat.find_spec h
      omega
    · intro p hp h1 h2 h3
      by_contra hne
      have := Nat.find_le (h := h) ⟨h1, h2, h3, hne⟩
      omega
  · refine ⟨le_rfl, ?_⟩
    intro p _ h1 h2 h3
    by_contra hne
    exact h ⟨p, h1, h2, h3, hne⟩

end Lem55Aux

open Lem55Aux in
theorem solution {α : Type*} [DecidableEq α] (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α)
    (hred : IsReduced 2 3 m σ S) :
    ∀ w' < eq4FirstFailure m σ S, -1 ≤ slack3 m σ S w' := by
  obtain ⟨_, hopt, hR1, _, _⟩ := hred
  have hS := hopt.1
  obtain ⟨hwle, heq4⟩ := eq4_before m σ S
  have hsl : ∀ t ≤ σ.length, slack3 m σ S t =
      3 * (policyMisses σ S t : ℤ) - (t : ℤ) - ((S t).card : ℤ) := by
    intro t ht
    unfold slack3 bank3
    rw [lru_misses _ σ hR1 t ht]
  -- one step of the slack
  have hstep : ∀ t < σ.length,
      slack3 m σ S t - 1 ≤ slack3 m σ S (t + 1) ∧
        (slack3 m σ S t + 1 ≤ slack3 m σ S (t + 1) ∨ 1 ≤ mu m σ S t) := by
    intro t ht
    rw [hsl t (le_of_lt ht), hsl (t + 1) ht, policyMisses_succ]
    have hsub := (hS.2 t ht).1
    by_cases hmem : σ[t] ∈ S t
    · have hmB : missB σ S t = false := by
        unfold missB
        rw [List.getElem?_eq_getElem ht]
        simp [hmem]
      have hc : (S (t + 1)).card ≤ (S t).card := by
        apply Finset.card_le_card
        rw [Finset.insert_eq_of_mem hmem] at hsub
        exact hsub
      have hmu : 1 ≤ mu m σ S t := by
        unfold mu
        apply Finset.one_le_card.2
        refine ⟨σ[t], Finset.mem_sdiff.2 ⟨hmem, ?_⟩⟩
        unfold lruCache
        rw [List.mem_toFinset]
        exact hR1 t ht
      rw [hmB]
      simp only [Bool.false_eq_true, if_false]
      refine ⟨by push_cast; omega, Or.inr hmu⟩
    · have hmB : missB σ S t = true := by
        unfold missB
        rw [List.getElem?_eq_getElem ht]
        simp [hmem]
      have hc : (S (t + 1)).card ≤ (S t).card + 1 :=
        le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)
      rw [hmB]
      simp only [if_true]
      refine ⟨by push_cast; omega, Or.inl (by push_cast; omega)⟩
  -- at positions ≡ 1 (mod 3) before the failure, the slack is at least μ
  have hanchor : ∀ p, p < eq4FirstFailure m σ S → 1 ≤ p → p % 3 = 1 →
      ((mu m σ S p : ℕ) : ℤ) ≤ slack3 m σ S p := by
    intro p hp h1 h3
    have h4 := heq4 p hp h1 (by omega) h3
    unfold Eq4At at h4
    unfold slack3
    push_cast at h4
    omega
  intro w' hw'
  have hw'n : w' ≤ σ.length := by omega
  rcases Nat.eq_zero_or_pos w' with h0 | hpos
  · subst h0
    rw [hsl 0 (Nat.zero_le _), hS.1]
    simp [policyMisses]
  · -- position right after an anchor
    have hnext : ∀ p, p < eq4FirstFailure m σ S → 1 ≤ p → p % 3 = 1 → p + 1 ≤ σ.length →
        0 ≤ slack3 m σ S (p + 1) := by
      intro p hp h1 h3 hpn
      have ha := hanchor p hp h1 h3
      obtain ⟨_, hor⟩ := hstep p (by omega)
      rcases hor with h | h
      · have : (0 : ℤ) ≤ ((mu m σ S p : ℕ) : ℤ) := Int.natCast_nonneg _
        omega
      · have : (1 : ℤ) ≤ ((mu m σ S p : ℕ) : ℤ) := by exact_mod_cast h
        have h2 := (hstep p (by omega)).1
        omega
    have hr : w' % 3 = 0 ∨ w' % 3 = 1 ∨ w' % 3 = 2 := by omega
    rcases hr with hr | hr | hr
    · -- w' = p + 2 with p ≡ 1
      have hw3 : 3 ≤ w' := by omega
      have h1 := hnext (w' - 2) (by omega) (by omega) (by omega) (by omega)
      have h2 := (hstep (w' - 1) (by omega)).1
      rw [show w' - 2 + 1 = w' - 1 by omega] at h1
      rw [show w' - 1 + 1 = w' by omega] at h2
      omega
    · have := hanchor w' hw' (by omega) hr
      have : (0 : ℤ) ≤ ((mu m σ S w' : ℕ) : ℤ) := Int.natCast_nonneg _
      omega
    · have h1 := hnext (w' - 1) (by omega) (by omega) (by omega) (by omega)
      rw [show w' - 1 + 1 = w' by omega] at h1
      omega
