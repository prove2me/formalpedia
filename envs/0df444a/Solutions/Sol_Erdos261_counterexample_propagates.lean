-- Prove2me | solution 1 for Erdos261.counterexample_propagates
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-23T18:47:19.312817+00:00
-- url     : https://prove2.me/submissions/a5f81971-7f5c-40ec-9b16-90af89580a0f

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset


open Finset

namespace E261
open Erdos261


/-- `f k = k / 2^k`. -/
def f (k : ℕ) : ℚ := k / 2 ^ k

lemma f_nonneg (k : ℕ) : 0 ≤ f k := by unfold f; positivity

lemma f_pos {k : ℕ} (hk : 1 ≤ k) : 0 < f k := by
  unfold f; have : (0:ℚ) < k := by exact_mod_cast hk
  positivity

lemma f_succ_le {m : ℕ} (hm : 1 ≤ m) : f (m+1) ≤ f m := by
  unfold f
  rw [pow_succ, div_le_div_iff₀ (by positivity) (by positivity)]
  have : (1:ℚ) ≤ m := by exact_mod_cast hm
  push_cast
  have h2 : (0:ℚ) < 2 ^ m := by positivity
  nlinarith

lemma f_succ_lt {m : ℕ} (hm : 2 ≤ m) : f (m+1) < f m := by
  unfold f
  rw [pow_succ, div_lt_div_iff₀ (by positivity) (by positivity)]
  have : (2:ℚ) ≤ m := by exact_mod_cast hm
  push_cast
  have h2 : (0:ℚ) < 2 ^ m := by positivity
  nlinarith

lemma f_anti {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : f b ≤ f a := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hb ih => exact (f_succ_le (le_trans ha hb)).trans ih

lemma f_strict {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) : f b < f a := by
  induction b, hab using Nat.le_induction with
  | base => exact f_succ_lt ha
  | succ b hb ih => exact (f_succ_le (by omega)).trans_lt ih

/-- Closed form of a finite block of consecutive terms. -/
lemma sum_Ioc_f (N d : ℕ) :
    ∑ k ∈ Ioc N (N + d), f k = (N + 2) / 2 ^ N - (N + d + 2) / 2 ^ (N + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show N + (d+1) = (N + d) + 1 by ring, Finset.sum_Ioc_succ_top (by omega), ih]
    unfold f
    push_cast
    rw [pow_succ]
    field_simp
    ring

/-- A representation of `n/2^n` by a finite set of indices all larger than `n`. -/
def Rep (n : ℕ) (S : Finset ℕ) : Prop := (∀ k ∈ S, n < k) ∧ f n = ∑ k ∈ S, f k

def RepP (n : ℕ) : Prop := ∃ S, Rep n S

/-- Tail of `S` beyond index `N`. -/
def tail (S : Finset ℕ) (N : ℕ) : ℚ := ∑ k ∈ S, if N < k then f k else 0

lemma tail_nonneg (S : Finset ℕ) (N : ℕ) : 0 ≤ tail S N := by
  unfold tail
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact f_nonneg k
  · exact le_rfl

lemma tail_split (S : Finset ℕ) (N : ℕ) :
    tail S N = (if N + 1 ∈ S then f (N+1) else 0) + tail S (N+1) := by
  unfold tail
  have : ∀ k, (if N < k then f k else 0)
      = (if N + 1 = k then f k else 0) + (if N + 1 < k then f k else 0) := by
    intro k
    by_cases h1 : N + 1 = k
    · subst h1; simp
    · by_cases h2 : N < k
      · have : N + 1 < k := by omega
        simp [h1, h2, this]
      · have : ¬ N + 1 < k := by omega
        simp [h1, h2, this]
  rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_add_distrib, Finset.sum_ite_eq]

lemma tail_lt (S : Finset ℕ) (N : ℕ) : 2 ^ N * tail S N < N + 2 := by
  set M := S.sup id
  have h1 : tail S N ≤ ∑ k ∈ Ioc N (N + M), f k := by
    unfold tail
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [Finset.mem_filter] at hk
      have : k ≤ M := Finset.le_sup (f := id) hk.1
      rw [Finset.mem_Ioc]; omega
    · intro k _ _; exact f_nonneg k
  rw [sum_Ioc_f] at h1
  have hp : (0:ℚ) < 2 ^ N := by positivity
  have hq : (0:ℚ) < ((N:ℚ) + M + 2) / 2 ^ (N + M) := by positivity
  calc 2 ^ N * tail S N ≤ 2 ^ N * ((N + 2) / 2 ^ N - (N + M + 2) / 2 ^ (N + M)) := by
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast h1) hp.le
    _ < 2 ^ N * ((N + 2) / 2 ^ N) := by
        apply mul_lt_mul_of_pos_left _ hp; push_cast; linarith
    _ = N + 2 := by field_simp

lemma tail_eventually_zero (S : Finset ℕ) (N : ℕ) (hN : S.sup id ≤ N) : tail S N = 0 := by
  unfold tail
  apply Finset.sum_eq_zero
  intro k hk
  have : k ≤ S.sup id := Finset.le_sup (f := id) hk
  have : ¬ N < k := by omega
  simp [this]

/-- The integer carry along a digit set `S`, started at `R_0 = n`. -/
def carry (n : ℕ) (S : Finset ℕ) : ℕ → ℤ
  | 0 => n
  | j + 1 => 2 * carry n S j - (if n + j + 1 ∈ S then ((n + j + 1 : ℕ) : ℤ) else 0)

/-- Carry identity: `R_j = 2^(n+j) * (tail of S beyond n+j)`. -/
lemma carry_eq {n : ℕ} {S : Finset ℕ} (h : Rep n S) (j : ℕ) :
    (carry n S j : ℚ) = 2 ^ (n + j) * tail S (n + j) := by
  induction j with
  | zero =>
    have ht : tail S n = f n := by
      rw [h.2]; unfold tail
      apply Finset.sum_congr rfl
      intro k hk; simp [h.1 k hk]
    simp only [carry, add_zero, ht, f]
    push_cast
    field_simp
  | succ j ih =>
    have hs := tail_split S (n + j)
    simp only [carry]
    push_cast
    rw [ih, show n + (j + 1) = n + j + 1 by ring]
    rw [hs]
    split_ifs with hm
    · unfold f; push_cast; rw [pow_succ]; field_simp; ring
    · rw [pow_succ]; ring

/-- Window lemma: along any representation, `0 ≤ R_j ≤ n + j + 1`. -/
lemma carry_window {n : ℕ} {S : Finset ℕ} (h : Rep n S) (j : ℕ) :
    0 ≤ carry n S j ∧ carry n S j ≤ (n + j + 1 : ℕ) := by
  have e := carry_eq h j
  constructor
  · have : (0:ℚ) ≤ carry n S j := by rw [e]; exact mul_nonneg (by positivity) (tail_nonneg _ _)
    exact_mod_cast this
  · have : (carry n S j : ℚ) < (n + j : ℕ) + 2 := by rw [e]; exact_mod_cast tail_lt S (n + j)
    have : carry n S j < ((n + j : ℕ) : ℤ) + 2 := by exact_mod_cast this
    push_cast at this ⊢; omega

lemma carry_eventually_zero {n : ℕ} {S : Finset ℕ} (h : Rep n S) :
    carry n S (S.sup id) = 0 := by
  have e := carry_eq h (S.sup id)
  rw [tail_eventually_zero S _ (by omega), mul_zero] at e
  exact_mod_cast e


/-- Remainder of a representation of `n/2^n` beyond the index `N`, as a representation. -/
lemma rep_restart {n : ℕ} {S : Finset ℕ} (h : Rep n S) (j : ℕ)
    (hc : carry n S j = ((n + j : ℕ) : ℤ)) : RepP (n + j) := by
  refine ⟨S.filter (fun k => n + j < k), ?_, ?_⟩
  · intro k hk; exact (Finset.mem_filter.1 hk).2
  · have e := carry_eq h j
    rw [hc] at e
    rw [Finset.sum_filter]
    change f (n + j) = tail S (n + j)
    unfold f
    have hp : (0:ℚ) < 2 ^ (n + j) := by positivity
    field_simp
    push_cast at e ⊢
    linarith

/-- Forward direction of the restart reduction. -/
theorem forward {n : ℕ} {S : Finset ℕ} (h : Rep n S) :
    (∃ j, greedy n j = 0) ∨
      ∃ j, Even (n + j) ∧ 2 * greedy n j = ((n + j + 2 : ℕ) : ℤ) ∧ RepP (n + j + 2) := by
  by_contra hP
  push Not at hP
  obtain ⟨hP1, hP2⟩ := hP
  have key : ∀ j, carry n S j = greedy n j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      have w1 := carry_window h (j + 1)
      have w2 := carry_window h (j + 2)
      simp only [carry, greedy] at w1 ⊢
      rw [ih] at w1 ⊢
      set R := greedy n j with hR
      by_cases hm : n + j + 1 ∈ S <;> by_cases hc : ((n + j + 1 : ℕ) : ℤ) ≤ 2 * R
      · rw [if_pos hm, if_pos hc]
      · exfalso; rw [if_pos hm] at w1; push_cast at w1 hc; omega
      · -- the only possible deviation
        exfalso
        simp only [hm, if_false, sub_zero] at w1
        push_cast at w1 hc
        rcases (show 2 * R = n + j + 1 ∨ 2 * R = n + j + 2 by omega) with h1 | h2
        · apply hP1 (j + 1)
          simp only [greedy]
          rw [← hR]
          push_cast
          rw [if_pos (by omega)]; omega
        · -- carry at j+2 forced to equal n+j+2
          have hm2 : n + (j + 1) + 1 ∈ S := by
            by_contra hm2
            have := w2.2
            simp only [carry] at this
            rw [ih] at this
            simp only [hm, hm2, if_false, sub_zero] at this
            push_cast at this; omega
          have hc2 : carry n S (j + 2) = ((n + j + 2 : ℕ) : ℤ) := by
            simp only [carry]
            rw [ih]
            simp only [hm, hm2, if_false, if_true, sub_zero]
            push_cast; omega
          have hr := rep_restart h (j + 2) (by rw [hc2]; push_cast; ring)
          apply hP2 j
          · have : Even ((n + j : ℕ) : ℤ) := ⟨R - 1, by push_cast; omega⟩
            exact (Int.even_coe_nat _).1 this
          · push_cast; omega
          · simpa [show n + (j + 2) = n + j + 2 by ring] using hr
      · rw [if_neg hm, if_neg hc, sub_zero]
  exact hP1 (S.sup id) (by rw [← key]; exact carry_eventually_zero h)

/-- Digit set produced by the greedy algorithm in its first `j` steps. -/
def gdig (n : ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | j + 1 => if ((n + j + 1 : ℕ) : ℤ) ≤ 2 * greedy n j then insert (n + j + 1) (gdig n j)
      else gdig n j

lemma gdig_sub (n : ℕ) : ∀ j, ∀ k ∈ gdig n j, n < k ∧ k ≤ n + j := by
  intro j
  induction j with
  | zero => simp [gdig]
  | succ j ih =>
    intro k hk
    simp only [gdig] at hk
    split_ifs at hk
    · rcases Finset.mem_insert.1 hk with h | h
      · omega
      · have := ih k h; omega
    · have := ih k hk; omega

lemma greedy_inv (n : ℕ) (j : ℕ) :
    f n = ∑ k ∈ gdig n j, f k + (greedy n j : ℚ) / 2 ^ (n + j) := by
  induction j with
  | zero => simp [gdig, greedy, f]
  | succ j ih =>
    have hnot : n + j + 1 ∉ gdig n j := by
      intro hh; have := gdig_sub n j _ hh; omega
    simp only [gdig, greedy]
    split_ifs with hc
    · rw [Finset.sum_insert hnot, ih]
      unfold f; push_cast
      rw [show n + (j+1) = n + j + 1 by ring, pow_succ]
      field_simp; ring
    · rw [ih]; push_cast
      rw [show n + (j+1) = n + j + 1 by ring, pow_succ]
      field_simp

/-- Backward direction: a greedy prefix plus a representation of the remaining carry. -/
lemma backward_general {n j : ℕ} (T : Finset ℕ) (hT : ∀ k ∈ T, n + j < k)
    (hv : (greedy n j : ℚ) / 2 ^ (n + j) = ∑ k ∈ T, f k) : RepP n := by
  have hd : Disjoint (gdig n j) T := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    have := gdig_sub n j k h1; have := hT k h2; omega
  refine ⟨gdig n j ∪ T, ?_, ?_⟩
  · intro k hk
    rcases Finset.mem_union.1 hk with h | h
    · exact (gdig_sub n j k h).1
    · have := hT k h; omega
  · rw [Finset.sum_union hd, ← hv]; exact greedy_inv n j

theorem backward {n : ℕ}
    (H : (∃ j, greedy n j = 0) ∨
      ∃ j, Even (n + j) ∧ 2 * greedy n j = ((n + j + 2 : ℕ) : ℤ) ∧ RepP (n + j + 2)) :
    RepP n := by
  rcases H with ⟨j, hj⟩ | ⟨j, _, hj, S', hS'1, hS'2⟩
  · exact backward_general (j := j) ∅ (by simp) (by simp [hj])
  · apply backward_general (j := j) (insert (n + j + 2) S')
    · intro k hk
      rcases Finset.mem_insert.1 hk with h | h
      · omega
      · have := hS'1 k h; omega
    · have hnot : n + j + 2 ∉ S' := fun hh => by have := hS'1 _ hh; omega
      rw [Finset.sum_insert hnot, ← hS'2]
      have hq : (greedy n j : ℚ) = ((n + j + 2 : ℕ) : ℚ) / 2 := by
        have : ((2 * greedy n j : ℤ) : ℚ) = ((n + j + 2 : ℕ) : ℚ) := by
          rw [hj]; push_cast; ring
        push_cast at this ⊢; linarith
      rw [hq]; unfold f
      push_cast
      rw [show n + j + 2 = (n + j) + 1 + 1 by ring, pow_succ, pow_succ]
      field_simp; ring

/-- The greedy carry from `(n,n)` stays in the strict window `0 ≤ R_j ≤ n + j`. -/
lemma greedy_window (n : ℕ) : ∀ j, 0 ≤ greedy n j ∧ greedy n j ≤ ((n + j : ℕ) : ℤ) := by
  intro j
  induction j with
  | zero => simp [greedy]
  | succ j ih =>
    simp only [greedy]
    split_ifs with hc <;> push_cast at ih hc ⊢ <;> omega

/-- Borwein–Loring form: the greedy carry is `R_{j+1} = 2 R_j mod (n + j + 1)`. -/
lemma greedy_succ_emod (n j : ℕ) :
    greedy n (j + 1) = (2 * greedy n j) % ((n + j + 1 : ℕ) : ℤ) := by
  obtain ⟨h0, h1⟩ := greedy_window n j
  simp only [greedy]
  split_ifs with hc
  · rw [show 2 * greedy n j = (2 * greedy n j - ((n + j + 1 : ℕ) : ℤ)) + ((n + j + 1 : ℕ) : ℤ) * 1
      by ring, Int.add_mul_emod_self_left, Int.emod_eq_of_lt]
    all_goals (push_cast at h1 hc ⊢; omega)
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]

/-- Restart reduction, in terms of `RepP`. -/
theorem repP_iff (n : ℕ) :
    RepP n ↔ (∃ j, greedy n j = 0) ∨
      ∃ j, Even (n + j) ∧ 2 * greedy n j = ((n + j + 2 : ℕ) : ℤ) ∧ RepP (n + j + 2) :=
  ⟨fun ⟨_, hS⟩ => forward hS, backward⟩

/-- Bridge: for `n ≥ 2`, `Erdos261Prop n ↔ RepP n`. -/
theorem erdos_iff_repP {n : ℕ} (hn : 2 ≤ n) : Erdos261Prop n ↔ RepP n := by
  constructor
  · rintro ⟨t, ht, a, hinj, hpos, hsum⟩
    have hpos' : ∀ i, 1 ≤ a i := fun i => hpos i
    have hsum' : f n = ∑ k, f (a k) := by simpa [f] using hsum
    refine ⟨Finset.univ.image a, ?_, ?_⟩
    · intro k hk
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hk
      by_contra hle
      push Not at hle
      -- pick another index
      obtain ⟨i', hi'⟩ : ∃ i' : Fin t, i' ≠ i := by
        by_cases h0 : i = ⟨0, by omega⟩
        · exact ⟨⟨1, by omega⟩, by rw [h0]; simp [Fin.ext_iff]⟩
        · exact ⟨⟨0, by omega⟩, fun e => h0 e.symm⟩
      have h1 : f n ≤ f (a i) := f_anti (hpos' i) hle
      have h2 : 0 < f (a i') := f_pos (hpos' i')
      have h3 : f (a i) + f (a i') ≤ ∑ k, f (a k) := by
        have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => f (a k))
          (Finset.subset_univ ({i, i'} : Finset (Fin t))) (fun k _ _ => f_nonneg _)
        rwa [Finset.sum_pair (Ne.symm hi')] at this
      linarith
    · rw [Finset.sum_image (fun x _ y _ hxy => hinj hxy)]; exact hsum'
  · rintro ⟨S, hS1, hS2⟩
    have hcard : 2 ≤ S.card := by
      by_contra hc
      push Not at hc
      interval_cases h : S.card
      · rw [Finset.card_eq_zero] at h
        rw [h, Finset.sum_empty] at hS2
        have := f_pos (show 1 ≤ n by omega); linarith
      · obtain ⟨k, rfl⟩ := Finset.card_eq_one.1 h
        rw [Finset.sum_singleton] at hS2
        have := f_strict hn (hS1 k (by simp)); linarith
    refine ⟨S.card, hcard, fun i => (S.equivFin.symm i : ℕ), ?_, ?_, ?_⟩
    · intro x y hxy
      exact S.equivFin.symm.injective (Subtype.ext hxy)
    · intro i
      have := hS1 _ (S.equivFin.symm i).2
      show 1 ≤ ((S.equivFin.symm i : S) : ℕ)
      omega
    · have : f n = ∑ i : Fin S.card, f ((S.equivFin.symm i : S) : ℕ) := by
        rw [hS2, ← Finset.sum_coe_sort S f]
        exact (Equiv.sum_comp S.equivFin.symm (fun x : S => f x)).symm
      simpa [f] using this

/-- **Restart reduction for Erdős #261.** For `n ≥ 2`, `n/2^n` is a sum of at least two
`a/2^a` with distinct positive `a` iff either the greedy carry from `(n,n)` reaches `0`, or the
greedy orbit passes a branch state `(N, N/2 + 1)` with `N = n + j` even such that the
instance `N + 2` is itself solvable. Non-greedy freedom is exactly this restart. -/
theorem restart_reduction {n : ℕ} (hn : 2 ≤ n) :
    Erdos261Prop n ↔ (∃ j, greedy n j = 0) ∨
      ∃ j, Even (n + j) ∧ 2 * greedy n j = ((n + j + 2 : ℕ) : ℤ) ∧
        Erdos261Prop (n + j + 2) := by
  rw [erdos_iff_repP hn, repP_iff]
  constructor
  · rintro (h | ⟨j, h1, h2, h3⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, h1, h2, (erdos_iff_repP (by omega)).2 h3⟩
  · rintro (h | ⟨j, h1, h2, h3⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, h1, h2, (erdos_iff_repP (by omega)).1 h3⟩

/-- A counterexample propagates along every restart branch of its greedy orbit. -/
theorem counterexample_propagates {n : ℕ} (hn : 2 ≤ n) (h : ¬ Erdos261Prop n) :
    (∀ j, greedy n j ≠ 0) ∧
      ∀ j, Even (n + j) → 2 * greedy n j = ((n + j + 2 : ℕ) : ℤ) → ¬ Erdos261Prop (n + j + 2) := by
  rw [restart_reduction hn] at h
  push Not at h
  exact ⟨h.1, fun j h1 h2 h3 => h.2 j h1 h2 h3⟩

end E261



namespace Erdos261

theorem counterexample_propagates {n : ℕ} (hn : 2 ≤ n) (h : ¬ Erdos261Prop n) :
    (∀ j, greedy n j ≠ 0) ∧
      ∀ j, Even (n + j) → 2 * greedy n j = ((n + j + 2 : ℕ) : ℤ) → ¬ Erdos261Prop (n + j + 2) :=
  E261.counterexample_propagates hn h

end Erdos261

open Erdos261 in
theorem solution {n : ℕ} (hn : 2 ≤ n) (h : ¬ Erdos261Prop n) :
    (∀ j, greedy n j ≠ 0) ∧
      ∀ j, Even (n + j) → 2 * greedy n j = ((n + j + 2 : ℕ) : ℤ) → ¬ Erdos261Prop (n + j + 2) :=
  Erdos261.counterexample_propagates hn h

#print axioms solution
