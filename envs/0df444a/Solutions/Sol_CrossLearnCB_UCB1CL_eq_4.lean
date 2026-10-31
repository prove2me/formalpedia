-- Prove2me | solution 1 for CrossLearnCB.UCB1CL.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T12:29:34.885377+00:00
-- url     : https://prove2.me/submissions/38e90757-09f3-40c1-a993-37ce01534dad

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Model

open MeasureTheory ProbabilityTheory

namespace UCB1CLEq4Aux
open CrossLearnCB.UCB1CL

/-- Successive pulls of arm `i` in contexts of `S` have strictly increasing `pullsIn` counts. -/
lemma pullsIn_lt {K C : ℕ} (ctx : ℕ → Fin C) (I : ℕ → Fin K) (i : Fin K)
    (S : Finset (Fin C)) {t t' : ℕ} (htt : t < t') (hi : I t = i) (hS : ctx t ∈ S) :
    pullsIn ctx I t i S < pullsIn ctx I t' i S := by
  classical
  unfold pullsIn
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_range] at hs ⊢
    exact ⟨by omega, hs.2⟩
  · intro h
    have : t ∈ (Finset.range t').filter (fun s => I s = i ∧ ctx s ∈ S) := by
      simp [htt, hi, hS]
    have := h this
    simp at this

lemma pullsIn_injOn {K C : ℕ} (ctx : ℕ → Fin C) (I : ℕ → Fin K) (i : Fin K)
    (S : Finset (Fin C)) (A : Finset ℕ) (hA : ∀ t ∈ A, I t = i ∧ ctx t ∈ S) :
    Set.InjOn (fun t => pullsIn ctx I t i S) A := by
  intro t ht t' ht' h
  simp only at h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := pullsIn_lt ctx I i S hlt (hA t ht).1 (hA t ht).2
    omega
  · have := pullsIn_lt ctx I i S hlt (hA t' ht').1 (hA t' ht').2
    omega

/-- A set of pulls in `S` whose `pullsIn` count is at most `m ≥ 0` has at most `m + 1` rounds. -/
lemma card_le_of_pullsIn_le {K C : ℕ} (ctx : ℕ → Fin C) (I : ℕ → Fin K) (i : Fin K)
    (S : Finset (Fin C)) (A : Finset ℕ) (hA : ∀ t ∈ A, I t = i ∧ ctx t ∈ S) (m : ℝ)
    (hm : 0 ≤ m) (hle : ∀ t ∈ A, (pullsIn ctx I t i S : ℝ) ≤ m) :
    (A.card : ℝ) ≤ m + 1 := by
  have hmaps : Set.MapsTo (fun t => pullsIn ctx I t i S) (A : Set ℕ)
      (Finset.range (⌊m⌋₊ + 1) : Set ℕ) := by
    intro t ht
    simp only [Finset.coe_range, Set.mem_Iio]
    have := hle t ht
    have : pullsIn ctx I t i S ≤ ⌊m⌋₊ := Nat.le_floor this
    omega
  have hcard := Finset.card_le_card_of_injOn _ hmaps (pullsIn_injOn ctx I i S A hA)
  simp only [Finset.card_range] at hcard
  have h1 : ((⌊m⌋₊ + 1 : ℕ) : ℝ) ≤ m + 1 := by
    push_cast
    linarith [Nat.floor_le hm]
  calc (A.card : ℝ) ≤ ((⌊m⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ m + 1 := h1

end UCB1CLEq4Aux

open CrossLearnCB.UCB1CL in
theorem solution {K C : ℕ} (gap : Fin K → Fin C → ℝ) (ctx : ℕ → Fin C) (I : ℕ → Fin K) (T : ℕ)
    (i : Fin K) (S : Finset (Fin C)) {n : ℕ} (e : Fin n → Fin C)
    (he : Function.Injective e) (hrange : Set.range e = ↑S)
    (hpos : ∀ k, 0 < gap i (e k))
    (hord : ∀ k l, k ≤ l → gap i (e l) ≤ gap i (e k)) (j : Fin n) :
    (∑ k ∈ Finset.univ.filter (fun k : Fin n => k ≤ j), (cliqueX gap ctx I T i S (e k) : ℝ))
      ≤ mThr T (gap i (e j)) + 1 := by
  classical
  set J := Finset.univ.filter (fun k : Fin n => k ≤ j) with hJ
  set m := mThr T (gap i (e j)) with hm
  have hlog : 0 ≤ Real.log T := Real.log_natCast_nonneg T
  have hm0 : 0 ≤ m := by
    simp only [hm, mThr]; positivity
  -- thresholds are monotone along the enumeration
  have hmono : ∀ k ∈ J, mThr T (gap i (e k)) ≤ m := by
    intro k hk
    simp only [hJ, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have h1 := hord k j hk
    have h2 := hpos j
    simp only [hm, mThr]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ h2.le h1 2
  -- the union of the counted rounds
  let A : Finset ℕ := (Finset.range T).filter (fun t => ∃ k ∈ J, ctx t = e k ∧ I t = i ∧
      (pullsIn ctx I t i S : ℝ) ≤ mThr T (gap i (e k)))
  have hsum : (∑ k ∈ J, (cliqueX gap ctx I T i S (e k) : ℝ)) = (A.card : ℝ) := by
    have : A = J.biUnion (fun k => (Finset.range T).filter (fun t => ctx t = e k ∧ I t = i ∧
        (pullsIn ctx I t i S : ℝ) ≤ mThr T (gap i (e k)))) := by
      ext t
      simp only [A, Finset.mem_filter, Finset.mem_biUnion]
      constructor
      · rintro ⟨h1, k, hk, h2⟩; exact ⟨k, hk, h1, h2⟩
      · rintro ⟨k, hk, h1, h2⟩; exact ⟨h1, k, hk, h2⟩
    rw [this, Finset.card_biUnion]
    · push_cast; rfl
    · intro k _ l _ hkl
      rw [Function.onFun, Finset.disjoint_left]
      intro t h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact hkl (he (h1.2.1.symm.trans h2.2.1))
  rw [hsum]
  apply UCB1CLEq4Aux.card_le_of_pullsIn_le ctx I i S A _ m hm0
  · intro t ht
    simp only [A, Finset.mem_filter] at ht
    obtain ⟨_, k, hk, _, _, h3⟩ := ht
    exact h3.trans (hmono k hk)
  · intro t ht
    simp only [A, Finset.mem_filter] at ht
    obtain ⟨_, k, _, h1, h2, _⟩ := ht
    refine ⟨h2, ?_⟩
    have : e k ∈ Set.range e := ⟨k, rfl⟩
    rw [hrange] at this
    rw [h1]; exact_mod_cast this
