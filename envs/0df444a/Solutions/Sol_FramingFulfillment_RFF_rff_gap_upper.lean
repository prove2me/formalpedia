-- Prove2me | solution 1 for FramingFulfillment.RFF.rff_gap_upper
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T15:57:01.953214+00:00
-- url     : https://prove2.me/submissions/5eb59647-140f-4437-b338-5b9139817d02

import Mathlib
import Definitions.Def_FramingFulfillment_RFF_Model
import Theorems.Thm_FramingFulfillment_RFF_lemma_3

open FramingFulfillment.RFF Finset

namespace RFFGap

section S0

variable (Q : Inst)

/-- number of stocked-out (product, FC) pairs -/
noncomputable def nEmpty (C : Q.Inv) : ℕ :=
  (univ.filter (fun p : Fin Q.I × Fin Q.K => C p.1 p.2 = 0)).card

noncomputable def wt (C : Q.Inv) (p : Fin Q.I × Fin Q.K) : ℝ :=
  if C p.1 p.2 = 0 then 2 * ((Q.I * Q.K : ℕ) : ℝ) - 2 * (nEmpty Q C : ℝ) + 2
  else 2 * ((Q.I * Q.K : ℕ) : ℝ) - 2 * (nEmpty Q C : ℝ) + 1

/-- the potential -/
noncomputable def pot (C N : Q.Inv) : ℝ :=
  ∑ p : Fin Q.I × Fin Q.K, wt Q C p * max 0 ((N p.1 p.2 : ℝ) - (C p.1 p.2 : ℝ))

def addE (N : Q.Inv) (i : Fin Q.I) (k : Fin Q.K) : Q.Inv :=
  fun a b => N a b + if a = i ∧ b = k then 1 else 0

lemma nEmpty_le (C : Q.Inv) : nEmpty Q C ≤ Q.I * Q.K := by
  unfold nEmpty
  calc _ ≤ (univ : Finset (Fin Q.I × Fin Q.K)).card := Finset.card_le_univ _
    _ = Q.I * Q.K := by simp

lemma wt_ge_one (C : Q.Inv) (p : Fin Q.I × Fin Q.K) : 1 ≤ wt Q C p := by
  have h : (nEmpty Q C : ℝ) ≤ ((Q.I * Q.K : ℕ) : ℝ) := by exact_mod_cast nEmpty_le Q C
  unfold wt; split_ifs <;> linarith

lemma wt_le (C : Q.Inv) (p : Fin Q.I × Fin Q.K) :
    wt Q C p ≤ 2 * ((Q.I * Q.K : ℕ) : ℝ) + 2 := by
  have h : (0 : ℝ) ≤ (nEmpty Q C : ℝ) := Nat.cast_nonneg _
  unfold wt; split_ifs <;> linarith

lemma pot_nonneg (C N : Q.Inv) : 0 ≤ pot Q C N :=
  Finset.sum_nonneg fun p _ =>
    mul_nonneg (le_trans zero_le_one (wt_ge_one Q C p)) (le_max_left _ _)

lemma pot_le (C N : Q.Inv) : pot Q C N ≤ (2 * ((Q.I * Q.K : ℕ) : ℝ) + 2) *
    ∑ p : Fin Q.I × Fin Q.K, max 0 ((N p.1 p.2 : ℝ) - (C p.1 p.2 : ℝ)) := by
  unfold pot
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun p _ =>
    mul_le_mul_of_nonneg_right (wt_le Q C p) (le_max_left _ _)

lemma empties_sub (C : Q.Inv) (i : Fin Q.I) (k : Fin Q.K) (h : 0 < C i k) :
    (univ.filter (fun p : Fin Q.I × Fin Q.K => C p.1 p.2 = 0)) ⊆
      (univ.filter (fun p : Fin Q.I × Fin Q.K => Q.take C i k p.1 p.2 = 0)) := by
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  unfold Inst.take
  split_ifs with h'
  · obtain ⟨h1, h2⟩ := h'
    rw [h1, h2] at hp; omega
  · exact hp

lemma nEmpty_take (C : Q.Inv) (i : Fin Q.I) (k : Fin Q.K) (h : 0 < C i k) :
    nEmpty Q C + (if C i k = 1 then 1 else 0) ≤ nEmpty Q (Q.take C i k) := by
  unfold nEmpty
  split_ifs with h1
  · have hss : (univ.filter (fun p : Fin Q.I × Fin Q.K => C p.1 p.2 = 0)) ⊂
        (univ.filter (fun p : Fin Q.I × Fin Q.K => Q.take C i k p.1 p.2 = 0)) := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨empties_sub Q C i k h, fun heq => ?_⟩
      have hmem : (i, k) ∈ (univ.filter (fun p : Fin Q.I × Fin Q.K =>
          Q.take C i k p.1 p.2 = 0)) := by
        simp [Inst.take, h1]
      rw [← heq] at hmem
      simp at hmem; omega
    have := Finset.card_lt_card hss
    omega
  · simpa using Finset.card_le_card (empties_sub Q C i k h)

lemma take_ne (C : Q.Inv) (i : Fin Q.I) (k : Fin Q.K) (p : Fin Q.I × Fin Q.K)
    (hp : p ≠ (i, k)) : Q.take C i k p.1 p.2 = C p.1 p.2 := by
  unfold Inst.take
  rw [if_neg]
  rintro ⟨h1, h2⟩
  exact hp (Prod.ext h1 h2)

lemma take_eq (C : Q.Inv) (i : Fin Q.I) (k : Fin Q.K) :
    Q.take C i k i k = C i k - 1 := by
  simp [Inst.take]

lemma addE_ne (N : Q.Inv) (i : Fin Q.I) (k : Fin Q.K) (p : Fin Q.I × Fin Q.K)
    (hp : p ≠ (i, k)) : addE Q N i k p.1 p.2 = N p.1 p.2 := by
  unfold addE
  rw [if_neg, add_zero]
  rintro ⟨h1, h2⟩
  exact hp (Prod.ext h1 h2)

lemma addE_eq (N : Q.Inv) (i : Fin Q.I) (k : Fin Q.K) : addE Q N i k i k = N i k + 1 := by
  simp [addE]

/-- weights only decrease when one unit is removed -/
lemma wt_take_le (C : Q.Inv) (i : Fin Q.I) (k : Fin Q.K) (h : 0 < C i k)
    (p : Fin Q.I × Fin Q.K) : wt Q (Q.take C i k) p ≤ wt Q C p := by
  have hm := nEmpty_take Q C i k h
  have hm' : (nEmpty Q C : ℝ) + (if C i k = 1 then 1 else 0) ≤ nEmpty Q (Q.take C i k) := by
    have : ((nEmpty Q C + (if C i k = 1 then 1 else 0) : ℕ) : ℝ) ≤ nEmpty Q (Q.take C i k) :=
      by exact_mod_cast hm
    push_cast at this; convert this using 2
  by_cases hp : p = (i, k)
  · subst hp
    simp only [wt, take_eq]
    by_cases h1 : C i k = 1
    · rw [if_pos h1] at hm'
      have : C i k - 1 = 0 := by omega
      simp only [this, if_true, show ¬ C i k = 0 by omega, if_false]
      linarith
    · rw [if_neg h1] at hm'
      have : ¬ C i k - 1 = 0 := by omega
      simp only [this, if_false, show ¬ C i k = 0 by omega]
      linarith
  · have hge : (nEmpty Q C : ℝ) ≤ nEmpty Q (Q.take C i k) := by
      have : (0:ℝ) ≤ (if C i k = 1 then 1 else 0) := by split_ifs <;> norm_num
      linarith
    simp only [wt, take_ne Q C i k p hp]
    split_ifs <;> linarith

/-- (1) serving a nominal request from stock -/
lemma pot_serve (C N : Q.Inv) (i : Fin Q.I) (k : Fin Q.K) (h : 0 < C i k) :
    pot Q (Q.take C i k) N ≤ pot Q C (addE Q N i k) := by
  unfold pot
  refine Finset.sum_le_sum fun p _ => ?_
  have hD : ((N p.1 p.2 : ℝ) - (Q.take C i k p.1 p.2 : ℝ)) =
      ((addE Q N i k p.1 p.2 : ℝ) - (C p.1 p.2 : ℝ)) := by
    by_cases hp : p = (i, k)
    · subst hp; simp only [take_eq, addE_eq]; push_cast [Nat.cast_sub h]; ring
    · rw [take_ne Q C i k p hp, addE_ne Q N i k p hp]
  rw [hD]
  exact mul_le_mul_of_nonneg_right (wt_take_le Q C i k h p) (le_max_left _ _)

/-- (3) a request at a stocked-out pair, nothing consumed -/
lemma pot_hit_none (C N : Q.Inv) (i : Fin Q.I) (k : Fin Q.K) (h : C i k = 0) :
    pot Q C N + 1 ≤ pot Q C (addE Q N i k) := by
  unfold pot
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (i, k)),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (i, k))]
  have hrest : (∑ p ∈ univ.erase (i, k), wt Q C p * max 0 ((N p.1 p.2 : ℝ) - C p.1 p.2)) =
      ∑ p ∈ univ.erase (i, k), wt Q C p * max 0 ((addE Q N i k p.1 p.2 : ℝ) - C p.1 p.2) :=
    Finset.sum_congr rfl fun p hp => by rw [addE_ne Q N i k p (Finset.ne_of_mem_erase hp)]
  rw [hrest]
  simp only [addE_eq, h]
  have hw := wt_ge_one Q C (i, k)
  have hN : (0:ℝ) ≤ N i k := Nat.cast_nonneg _
  push_cast
  rw [max_eq_right (by linarith), max_eq_right (by linarith)]
  nlinarith

/-- (2) a request at a stocked-out pair, rerouted to a stocked pair -/
lemma pot_hit_reroute (C N : Q.Inv) (i : Fin Q.I) (k : Fin Q.K) (h : C i k = 0)
    (i' : Fin Q.I) (k' : Fin Q.K) (h' : 0 < C i' k') :
    pot Q (Q.take C i' k') N + 1 ≤ pot Q C (addE Q N i k) := by
  have hne : (i', k') ≠ (i, k) := by
    intro he; simp only [Prod.mk.injEq] at he; rw [he.1, he.2] at h'; omega
  have hm := nEmpty_take Q C i' k' h'
  have hm' : (nEmpty Q C : ℝ) + (if C i' k' = 1 then 1 else 0) ≤
      nEmpty Q (Q.take C i' k') := by
    have : ((nEmpty Q C + (if C i' k' = 1 then 1 else 0) : ℕ) : ℝ) ≤
        nEmpty Q (Q.take C i' k') := by exact_mod_cast hm
    push_cast at this; convert this using 2
  set m := (nEmpty Q C : ℝ)
  set m' := (nEmpty Q (Q.take C i' k') : ℝ)
  have hmm : m ≤ m' := by
    have : (0:ℝ) ≤ (if C i' k' = 1 then 1 else 0) := by split_ifs <;> norm_num
    linarith
  set PP := ((Q.I * Q.K : ℕ) : ℝ)
  have hmP : m ≤ PP := by simp only [m, PP]; exact_mod_cast nEmpty_le Q C
  -- termwise comparison with bonuses
  let bonus : Fin Q.I × Fin Q.K → ℝ := fun p =>
    (if p = (i, k) then 2 * PP - 2 * m + 2 else 0) +
    (if p = (i', k') then -(2 * PP - 2 * m + 1) else 0)
  have hterm : ∀ p, wt Q (Q.take C i' k') p * max 0 ((N p.1 p.2 : ℝ) - Q.take C i' k' p.1 p.2)
      + bonus p ≤ wt Q C p * max 0 ((addE Q N i k p.1 p.2 : ℝ) - C p.1 p.2) := by
    intro p
    by_cases hp : p = (i, k)
    · subst hp
      have hp2 : (i, k) ≠ (i', k') := fun he => hne he.symm
      simp only [bonus, if_true, if_neg hp2, add_zero]
      rw [take_ne Q C i' k' (i, k) hp2, addE_eq]
      simp only [h, Nat.cast_zero, sub_zero]
      have hN : (0:ℝ) ≤ N i k := Nat.cast_nonneg _
      push_cast
      rw [max_eq_right hN, max_eq_right (by linarith)]
      have hw1 : wt Q (Q.take C i' k') (i, k) ≤ wt Q C (i, k) :=
        wt_take_le Q C i' k' h' (i, k)
      have hw2 : wt Q C (i, k) = 2 * PP - 2 * m + 2 := by simp only [wt, h, if_true]; rfl
      nlinarith
    · by_cases hp' : p = (i', k')
      · subst hp'
        simp only [bonus, if_neg hp, if_true, zero_add]
        rw [take_eq, addE_ne Q N i k (i', k') hp]
        have hw2 : wt Q C (i', k') = 2 * PP - 2 * m + 1 := by
          simp only [wt, show ¬ C i' k' = 0 by omega, if_false]; rfl
        have hwt' : wt Q (Q.take C i' k') (i', k') ≤ 2 * PP - 2 * m + 1 := by
          rw [← hw2]; exact wt_take_le Q C i' k' h' _
        have hwt1 := wt_ge_one Q (Q.take C i' k') (i', k')
        push_cast [Nat.cast_sub h']
        -- max 0 (N - (C-1)) ≤ max 0 (N - C) + 1
        have hmax : max 0 ((N i' k' : ℝ) - ((C i' k' : ℝ) - 1)) ≤
            max 0 ((N i' k' : ℝ) - C i' k') + 1 := by
          rcases le_total 0 ((N i' k' : ℝ) - C i' k') with hh | hh
          · rw [max_eq_right hh, max_eq_right (by linarith)]; linarith
          · rw [max_eq_left hh]; exact max_le (by norm_num) (by linarith)
        have h0 : 0 ≤ max 0 ((N i' k' : ℝ) - C i' k') := le_max_left _ _
        -- case split on whether the weight drops
        by_cases h1 : C i' k' = 1
        · rw [if_pos h1] at hm'
          have hwt'' : wt Q (Q.take C i' k') (i', k') ≤ 2 * PP - 2 * m := by
            have : Q.take C i' k' i' k' = 0 := by rw [take_eq]; omega
            simp only [wt, this, if_true]
            linarith
          have hm0 : 0 ≤ 2 * PP - 2 * m := by linarith
          nlinarith [mul_le_mul_of_nonneg_left hmax (le_trans zero_le_one hwt1)]
        · nlinarith [mul_le_mul_of_nonneg_left hmax (le_trans zero_le_one hwt1)]
      · simp only [bonus, if_neg hp, if_neg hp', add_zero]
        rw [take_ne Q C i' k' p hp', addE_ne Q N i k p hp]
        exact mul_le_mul_of_nonneg_right (wt_take_le Q C i' k' h' p) (le_max_left _ _)
  have hsum := Finset.sum_le_sum fun p (_ : p ∈ (univ : Finset (Fin Q.I × Fin Q.K))) => hterm p
  rw [Finset.sum_add_distrib] at hsum
  have hb : ∑ p : Fin Q.I × Fin Q.K, bonus p = 1 := by
    simp only [bonus, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  unfold pot
  linarith


end S0

section S1

variable (Q : Inst)

/-- nominal demand probabilities for an arbitrary per-period weight array -/
noncomputable def Ex (q : Fin Q.T → Fin Q.I → Fin Q.K → ℝ) : ℕ → (Q.Inv → ℝ) → ℝ
  | 0, f => f 0
  | n + 1, f =>
      if h : n + 1 ≤ Q.T then
        (1 - ∑ i, ∑ k, q ⟨Q.T - (n + 1), by omega⟩ i k) * Ex q n f +
          ∑ i, ∑ k, q ⟨Q.T - (n + 1), by omega⟩ i k * Ex q n (fun N => f (addE Q N i k))
      else Ex q n f

variable {Q}
variable (q : Fin Q.T → Fin Q.I → Fin Q.K → ℝ)

lemma Ex_succ (n : ℕ) (h : n + 1 ≤ Q.T) (f : Q.Inv → ℝ) :
    Ex Q q (n + 1) f = (1 - ∑ i, ∑ k, q ⟨Q.T - (n + 1), by omega⟩ i k) * Ex Q q n f +
          ∑ i, ∑ k, q ⟨Q.T - (n + 1), by omega⟩ i k * Ex Q q n (fun N => f (addE Q N i k)) := by
  rw [Ex, dif_pos h]

lemma Ex_succ_of_gt (n : ℕ) (h : ¬ n + 1 ≤ Q.T) (f : Q.Inv → ℝ) :
    Ex Q q (n + 1) f = Ex Q q n f := by
  rw [Ex, dif_neg h]

variable (hq0 : ∀ t i k, 0 ≤ q t i k) (hq1 : ∀ t, ∑ i, ∑ k, q t i k ≤ 1)
include hq0 hq1

lemma Ex_mono : ∀ (n : ℕ) (f g : Q.Inv → ℝ), (∀ N, f N ≤ g N) → Ex Q q n f ≤ Ex Q q n g := by
  intro n
  induction n with
  | zero => intro f g h; exact h 0
  | succ n ih =>
    intro f g h
    by_cases hn : n + 1 ≤ Q.T
    · rw [Ex_succ q n hn, Ex_succ q n hn]
      refine add_le_add (mul_le_mul_of_nonneg_left (ih f g h) (by linarith [hq1 ⟨Q.T - (n + 1), by omega⟩]))
        (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (ih _ _ fun N => h _) (hq0 _ _ _))
    · rw [Ex_succ_of_gt q n hn, Ex_succ_of_gt q n hn]; exact ih f g h

omit hq0 hq1 in
lemma Ex_const : ∀ (n : ℕ) (a : ℝ), Ex Q q n (fun _ => a) = a := by
  intro n
  induction n with
  | zero => intro a; rfl
  | succ n ih =>
    intro a
    by_cases hn : n + 1 ≤ Q.T
    · rw [Ex_succ q n hn]
      simp only [ih]
      have : (∑ i, ∑ k, q ⟨Q.T - (n + 1), by omega⟩ i k * a) =
          (∑ i, ∑ k, q ⟨Q.T - (n + 1), by omega⟩ i k) * a := by simp only [Finset.sum_mul]
      rw [this]; ring
    · rw [Ex_succ_of_gt q n hn, ih]

omit hq0 hq1 in
lemma Ex_add : ∀ (n : ℕ) (f g : Q.Inv → ℝ),
    Ex Q q n (fun N => f N + g N) = Ex Q q n f + Ex Q q n g := by
  intro n
  induction n with
  | zero => intro f g; rfl
  | succ n ih =>
    intro f g
    by_cases hn : n + 1 ≤ Q.T
    · rw [Ex_succ q n hn, Ex_succ q n hn, Ex_succ q n hn]
      simp only [ih, mul_add, Finset.sum_add_distrib]
      ring
    · rw [Ex_succ_of_gt q n hn, Ex_succ_of_gt q n hn, Ex_succ_of_gt q n hn, ih]

omit hq0 hq1 in
lemma Ex_smul : ∀ (n : ℕ) (c : ℝ) (f : Q.Inv → ℝ),
    Ex Q q n (fun N => c * f N) = c * Ex Q q n f := by
  intro n
  induction n with
  | zero => intro c f; rfl
  | succ n ih =>
    intro c f
    by_cases hn : n + 1 ≤ Q.T
    · rw [Ex_succ q n hn, Ex_succ q n hn]
      simp only [ih]
      rw [mul_add, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun i _ => by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    · rw [Ex_succ_of_gt q n hn, Ex_succ_of_gt q n hn, ih]

omit hq0 hq1 in
lemma Ex_sum {ι : Type*} (s : Finset ι) (f : ι → Q.Inv → ℝ) (n : ℕ) :
    Ex Q q n (fun N => ∑ a ∈ s, f a N) = ∑ a ∈ s, Ex Q q n (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Ex_const q n 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [Ex_add q n (f a) (fun N => ∑ x ∈ s, f x N), ih]

omit hq0 hq1 in
lemma Ex_sub (n : ℕ) (f g : Q.Inv → ℝ) :
    Ex Q q n (fun N => f N - g N) = Ex Q q n f - Ex Q q n g := by
  have := Ex_add q n f (fun N => -1 * g N)
  rw [Ex_smul q n (-1) g] at this
  simp only [neg_one_mul, ← sub_eq_add_neg] at this
  rw [this]

/-- cumulative nominal mass of the last `n` periods at one pair -/
noncomputable def mu (i0 : Fin Q.I) (k0 : Fin Q.K) (n : ℕ) : ℝ :=
  ∑ t : Fin Q.T, if Q.T - n ≤ t.val then q t i0 k0 else 0

omit hq0 hq1 in
lemma mu_succ (i0 : Fin Q.I) (k0 : Fin Q.K) (n : ℕ) (h : n + 1 ≤ Q.T) :
    mu q i0 k0 (n + 1) = q ⟨Q.T - (n + 1), by omega⟩ i0 k0 + mu q i0 k0 n := by
  unfold mu
  set t0 : Fin Q.T := ⟨Q.T - (n + 1), by omega⟩
  calc (∑ t : Fin Q.T, if Q.T - (n + 1) ≤ t.val then q t i0 k0 else 0) =
      ∑ t : Fin Q.T, ((if t0 = t then q t i0 k0 else 0) +
        (if Q.T - n ≤ t.val then q t i0 k0 else 0)) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases h1 : t0 = t
        · subst h1
          simp only [t0, if_true, le_refl, show ¬ (Q.T - n ≤ Q.T - (n + 1)) by omega, if_false,
            add_zero]
        · have h2 : t.val ≠ Q.T - (n + 1) := fun h' => h1 (Fin.ext h'.symm)
          by_cases h3 : Q.T - n ≤ t.val
          · rw [if_pos (by omega), if_neg h1, if_pos h3, zero_add]
          · rw [if_neg (by omega), if_neg h1, if_neg h3, add_zero]
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_ite_eq]; simp

omit hq0 hq1 in
lemma mu_zero (i0 : Fin Q.I) (k0 : Fin Q.K) : mu q i0 k0 0 = 0 := by
  unfold mu
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [if_neg]
  have := t.2; omega

omit hq0 hq1 in
lemma Ex_mean (i0 : Fin Q.I) (k0 : Fin Q.K) : ∀ n, n ≤ Q.T →
    Ex Q q n (fun N => (N i0 k0 : ℝ)) = mu q i0 k0 n := by
  intro n
  induction n with
  | zero => intro _; simp [Ex, mu_zero]
  | succ n ih =>
    intro hn
    rw [Ex_succ q n hn, mu_succ q i0 k0 n hn]
    have hsh : ∀ i k, Ex Q q n (fun N => ((addE Q N i k i0 k0 : ℕ) : ℝ)) =
        mu q i0 k0 n + (if i0 = i ∧ k0 = k then 1 else 0) := by
      intro i k
      have : (fun N : Q.Inv => ((addE Q N i k i0 k0 : ℕ) : ℝ)) =
          fun N => (N i0 k0 : ℝ) + (if i0 = i ∧ k0 = k then (1:ℝ) else 0) := by
        funext N; simp only [addE]; push_cast; split_ifs <;> simp
      rw [this, Ex_add q n, ih (by omega), Ex_const]
    simp only [hsh, ih (by omega), mul_add, Finset.sum_add_distrib]
    have hS : (∑ i, ∑ k, q ⟨Q.T - (n + 1), by omega⟩ i k * mu q i0 k0 n) =
        (∑ i, ∑ k, q ⟨Q.T - (n + 1), by omega⟩ i k) * mu q i0 k0 n := by
      simp only [Finset.sum_mul]
    rw [hS]
    have : (∑ i, ∑ k, q ⟨Q.T - (n + 1), by omega⟩ i k * (if i0 = i ∧ k0 = k then (1:ℝ) else 0)) =
        q ⟨Q.T - (n + 1), by omega⟩ i0 k0 := by
      rw [Finset.sum_eq_single i0]
      · rw [Finset.sum_eq_single k0]
        · simp
        · intro b _ hb; simp [Ne.symm hb]
        · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    rw [this]; ring

lemma Ex_var (i0 : Fin Q.I) (k0 : Fin Q.K) : ∀ n, n ≤ Q.T →
    Ex Q q n (fun N => ((N i0 k0 : ℝ) - mu q i0 k0 n) ^ 2) ≤ mu q i0 k0 n := by
  intro n
  induction n with
  | zero => intro _; simp [Ex, mu_zero]
  | succ n ih =>
    intro hn
    rw [Ex_succ q n hn, mu_succ q i0 k0 n hn]
    have hmean := Ex_mean q i0 k0 n (by omega)
    set m := mu q i0 k0 n
    set qq := q ⟨Q.T - (n + 1), by omega⟩ i0 k0 with hqq
    have hshift : ∀ b : ℝ, Ex Q q n (fun N => ((N i0 k0 : ℝ) - m + b) ^ 2) =
        Ex Q q n (fun N => ((N i0 k0 : ℝ) - m) ^ 2) + b ^ 2 := by
      intro b
      have e : (fun N : Q.Inv => ((N i0 k0 : ℝ) - m + b) ^ 2) = fun N =>
          ((N i0 k0 : ℝ) - m) ^ 2 + ((2 * b) * (N i0 k0 : ℝ) + (b ^ 2 - 2 * b * m)) := by
        funext N; ring
      rw [e, Ex_add q n, Ex_add q n, Ex_smul q n, hmean, Ex_const]; ring
    have hf : ∀ i k, Ex Q q n (fun N => ((addE Q N i k i0 k0 : ℕ) - (qq + m) : ℝ) ^ 2) =
        Ex Q q n (fun N => ((N i0 k0 : ℝ) - m) ^ 2) +
          (if i0 = i ∧ k0 = k then (1 - qq) ^ 2 else qq ^ 2) := by
      intro i k
      by_cases hik : i0 = i ∧ k0 = k
      · rw [if_pos hik, ← hshift (1 - qq)]
        congr 1; funext N; simp only [addE, if_pos hik]; push_cast; ring
      · rw [if_neg hik, show qq ^ 2 = (-qq) ^ 2 by ring, ← hshift (-qq)]
        congr 1; funext N; simp only [addE, if_neg hik]; push_cast; ring
    have h0 : Ex Q q n (fun N => ((N i0 k0 : ℝ) - (qq + m)) ^ 2) =
        Ex Q q n (fun N => ((N i0 k0 : ℝ) - m) ^ 2) + qq ^ 2 := by
      rw [show qq ^ 2 = (-qq) ^ 2 by ring, ← hshift (-qq)]; congr 1; funext N; ring
    simp only [hf, h0, mul_add, Finset.sum_add_distrib]
    set V := Ex Q q n (fun N => ((N i0 k0 : ℝ) - m) ^ 2)
    set Sq := ∑ i, ∑ k, q ⟨Q.T - (n + 1), by omega⟩ i k
    have hsumV : (∑ i, ∑ k, q ⟨Q.T - (n + 1), by omega⟩ i k * V) = Sq * V := by
      simp only [Sq, Finset.sum_mul]
    have hsumI : (∑ i, ∑ k, q ⟨Q.T - (n + 1), by omega⟩ i k *
        (if i0 = i ∧ k0 = k then (1 - qq) ^ 2 else qq ^ 2)) =
        Sq * qq ^ 2 + qq * ((1 - qq) ^ 2 - qq ^ 2) := by
      have e : ∀ i k, q ⟨Q.T - (n + 1), by omega⟩ i k *
          (if i0 = i ∧ k0 = k then (1 - qq) ^ 2 else qq ^ 2) =
          q ⟨Q.T - (n + 1), by omega⟩ i k * qq ^ 2 +
            (if i0 = i ∧ k0 = k then qq * ((1 - qq) ^ 2 - qq ^ 2) else 0) := by
        intro i k
        split_ifs with hh
        · obtain ⟨rfl, rfl⟩ := hh; ring
        · ring
      simp only [e, Finset.sum_add_distrib, Sq, Finset.sum_mul]
      congr 1
      rw [Finset.sum_eq_single i0]
      · rw [Finset.sum_eq_single k0]
        · simp
        · intro b _ hb; simp [Ne.symm hb]
        · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    rw [hsumV, hsumI]
    have hih := ih (by omega)
    have hq0' : 0 ≤ qq := hq0 _ _ _
    have hSq : qq ≤ Sq := by
      simp only [Sq, qq]
      calc q ⟨Q.T - (n + 1), by omega⟩ i0 k0 ≤ ∑ k, q ⟨Q.T - (n + 1), by omega⟩ i0 k :=
            Finset.single_le_sum (f := fun k => q ⟨Q.T - (n + 1), by omega⟩ i0 k)
              (fun k _ => hq0 _ _ _) (Finset.mem_univ k0)
        _ ≤ _ := Finset.single_le_sum (f := fun i => ∑ k, q ⟨Q.T - (n + 1), by omega⟩ i k)
              (fun i _ => Finset.sum_nonneg fun k _ => hq0 _ _ _) (Finset.mem_univ i0)
    nlinarith

lemma Ex_abs_le (n : ℕ) (h : Q.Inv → ℝ) :
    Ex Q q n (fun N => |h N|) ≤ Real.sqrt (Ex Q q n (fun N => h N ^ 2)) := by
  set a := Ex Q q n (fun N => |h N|)
  have ha : 0 ≤ a := by
    have := Ex_mono q hq0 hq1 n (fun _ => (0:ℝ)) (fun N => |h N|) (fun N => abs_nonneg _)
    rwa [Ex_const] at this
  have hsq : 0 ≤ Ex Q q n (fun N => (|h N| - a) ^ 2) := by
    have := Ex_mono q hq0 hq1 n (fun _ => (0:ℝ)) (fun N => (|h N| - a) ^ 2)
      (fun N => sq_nonneg _)
    rwa [Ex_const] at this
  have e : (fun N => (|h N| - a) ^ 2) = fun N => h N ^ 2 + ((-2 * a) * |h N| + a ^ 2) := by
    funext N; rw [← sq_abs (h N)]; ring
  rw [e, Ex_add q n, Ex_add q n, Ex_smul q n, Ex_const] at hsq
  apply Real.le_sqrt_of_sq_le
  nlinarith

/-- `E[(N_p - c)^+] ≤ √μ` when the mean `μ` is at most `c` -/
lemma Ex_excess_le (i0 : Fin Q.I) (k0 : Fin Q.K) (c : ℝ) (hc : mu q i0 k0 Q.T ≤ c) :
    Ex Q q Q.T (fun N => max 0 ((N i0 k0 : ℝ) - c)) ≤ Real.sqrt (mu q i0 k0 Q.T) := by
  calc _ ≤ Ex Q q Q.T (fun N => |(N i0 k0 : ℝ) - mu q i0 k0 Q.T|) :=
        Ex_mono q hq0 hq1 _ _ _ fun N => max_le (abs_nonneg _)
          (le_trans (by linarith) (le_abs_self _))
    _ ≤ Real.sqrt (Ex Q q Q.T (fun N => ((N i0 k0 : ℝ) - mu q i0 k0 Q.T) ^ 2)) :=
        Ex_abs_le q hq0 hq1 _ _
    _ ≤ _ := Real.sqrt_le_sqrt (Ex_var q hq0 hq1 i0 k0 Q.T le_rfl)


end S1

section S2

lemma fc_pos (Q : Inst) (C : Q.Inv) (j : Fin Q.J) (i : Fin Q.I) (k : Fin Q.K)
    (hs : ∑ k, C i k ≠ 0) : 0 < C i (Q.fcChoice C j i k) := by
  classical
  have hne : (univ.filter (fun k => 0 < C i k)).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hc
    apply hs
    exact Finset.sum_eq_zero fun k _ => by have := hc (Finset.mem_univ k); omega
  have hmem : Q.fcChoice C j i k ∈ univ.filter (fun k => 0 < C i k) := by
    simp only [Inst.fcChoice]
    split_ifs with h1 h2
    · simpa using h1
    · exact (Finset.mem_filter.1 (Finset.min'_mem _ _)).1
  simpa using hmem

lemma fc_of_pos (Q : Inst) (C : Q.Inv) (j : Fin Q.J) (i : Fin Q.I) (k : Fin Q.K)
    (h : 0 < C i k) : Q.fcChoice C j i k = k := by
  simp [Inst.fcChoice, h]

/-- One customer arrival from region `j` facing the sampled assignment `φ`:
the RFF continuation dominates the nominal (stock-out-free) accounting. -/
theorem step (Q : Inst) (hv : ∀ i j r, 0 ≤ Q.v i j r) (hv0 : ∀ i j, Q.v i j Q.noDisp = 0)
    (C : Q.Inv) (j : Fin Q.J) (φ : Fin Q.I → Fin Q.R)
    (yt : Fin Q.I → Fin Q.K → ℝ) (hyt0 : ∀ i k, 0 ≤ yt i k)
    (hyt1 : ∀ i, 0 < Q.buyProb j φ i → ∑ k, yt i k = 1)
    (R Ψ : Q.Inv → ℝ) (Ψe : Fin Q.I → Fin Q.K → ℝ) (G L pbar cbar Mx : ℝ)
    (hR : ∀ C', G - L * Ψ C' ≤ R C')
    (h1 : ∀ i k, 0 < C i k → Ψ (Q.take C i k) ≤ Ψe i k)
    (h2 : ∀ i k, C i k = 0 → ∀ i' k', 0 < C i' k' → Ψ (Q.take C i' k') + 1 ≤ Ψe i k)
    (hMxC : Ψ C ≤ Mx) (hMxT : ∀ i k, 0 < C i k → Ψ (Q.take C i k) ≤ Mx)
    (hMxe : ∀ i, ∑ k, C i k = 0 → ∀ k, Mx + 1 ≤ Ψe i k)
    (hp : ∀ i r, |Q.p i r| ≤ pbar) (hc : ∀ i k, |Q.c i j k| ≤ cbar)
    (hpb : 0 ≤ pbar) (hcb : 0 ≤ cbar) (hL : 2 * (pbar + cbar) ≤ L) :
    (∑ i, Q.buyProb j φ i * (Q.p i (φ i) + ∑ k, yt i k * (G - L * Ψe i k - Q.c i j k))) +
        (1 - ∑ i, Q.buyProb j φ i) * (G - L * Ψ C) ≤
      (∑ i, Q.buyProb j (Q.hideOut C φ) i * (Q.p i (Q.hideOut C φ i) +
        ∑ k, yt i k * (R (Q.take C i (Q.fcChoice C j i k)) - Q.c i j (Q.fcChoice C j i k)))) +
        (1 - ∑ i, Q.buyProb j (Q.hideOut C φ) i) * R C := by
  classical
  set φt := Q.hideOut C φ with hφt
  set b : Fin Q.I → ℝ := fun i => Q.buyProb j φ i with hb
  set bt : Fin Q.I → ℝ := fun i => Q.buyProb j φt i with hbt
  set V := ∑ l, Q.vPhi j φ l with hV
  set Vt := ∑ l, Q.vPhi j φt l with hVt
  have hL0 : 0 ≤ L := by linarith
  have hvt : ∀ l, Q.vPhi j φt l = if ∑ k, C l k = 0 then 0 else Q.vPhi j φ l := by
    intro l
    simp only [hφt, Inst.vPhi, Inst.hideOut]
    split_ifs with h
    · exact hv0 l j
    · rfl
  have hφt_ne : ∀ l, ¬ (∑ k, C l k = 0) → φt l = φ l := by
    intro l h; simp only [hφt, Inst.hideOut, if_neg h]
  have hvnn : ∀ l, 0 ≤ Q.vPhi j φ l := fun l => hv _ _ _
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun l _ => hvnn l
  have hVle : Vt ≤ V := by
    refine Finset.sum_le_sum fun l _ => ?_
    rw [hvt l]; split_ifs
    · exact hvnn l
    · exact le_rfl
  have hVt0 : 0 ≤ Vt := Finset.sum_nonneg fun l _ => by rw [hvt l]; split_ifs <;> simp [hvnn l]
  have hbt_hid : ∀ i, ∑ k, C i k = 0 → bt i = 0 := by
    intro i h; simp only [hbt, Inst.buyProb, hvt i, if_pos h, zero_div]
  have hb_nn : ∀ i, 0 ≤ b i := fun i => div_nonneg (hvnn i) (by linarith)
  have hbt_nn : ∀ i, 0 ≤ bt i := fun i => div_nonneg (hv _ _ _) (by linarith)
  have hbt_ge : ∀ i, ¬ (∑ k, C i k = 0) → b i ≤ bt i := by
    intro i h
    simp only [hb, hbt, Inst.buyProb, hvt i, if_neg h]
    exact div_le_div_of_nonneg_left (hvnn i) (by linarith) (by linarith)
  have hb0 : ∀ i, b i = 0 → bt i = 0 := by
    intro i h
    have hvi : Q.vPhi j φ i = 0 := by
      simp only [hb, Inst.buyProb] at h
      rcases div_eq_zero_iff.1 h with h' | h'
      · exact h'
      · linarith
    simp only [hbt, Inst.buyProb, hvt i, hvi]; split_ifs <;> simp
  have hsumb : ∑ i, b i = V / (1 + V) := by simp only [hb, Inst.buyProb, ← Finset.sum_div]; rfl
  have hsumbt : ∑ i, bt i = Vt / (1 + Vt) := by simp only [hbt, Inst.buyProb, ← Finset.sum_div]; rfl
  have hsum_le : ∑ i, bt i ≤ ∑ i, b i := by
    rw [hsumb, hsumbt, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hsumbt1 : ∑ i, bt i ≤ 1 := by
    rw [hsumbt, div_le_one (by linarith)]; linarith
  -- Step A: replace R by its lower bound
  set Y : Fin Q.I → ℝ := fun i => Q.p i (φt i) +
      ∑ k, yt i k * (G - L * Ψ (Q.take C i (Q.fcChoice C j i k)) - Q.c i j (Q.fcChoice C j i k))
    with hY
  set Z : Fin Q.I → ℝ := fun i => Q.p i (φ i) + ∑ k, yt i k * (G - L * Ψe i k - Q.c i j k)
    with hZ
  have hA : (∑ i, bt i * Y i) + (1 - ∑ i, bt i) * (G - L * Ψ C) ≤
      (∑ i, bt i * (Q.p i (φt i) +
        ∑ k, yt i k * (R (Q.take C i (Q.fcChoice C j i k)) - Q.c i j (Q.fcChoice C j i k)))) +
        (1 - ∑ i, bt i) * R C := by
    refine add_le_add (Finset.sum_le_sum fun i _ => ?_)
      (mul_le_mul_of_nonneg_left (hR C) (by linarith))
    refine mul_le_mul_of_nonneg_left ?_ (hbt_nn i)
    simp only [hY]
    refine (add_le_add_iff_left _).2 (Finset.sum_le_sum fun k _ => ?_)
    exact mul_le_mul_of_nonneg_left (by linarith [hR (Q.take C i (Q.fcChoice C j i k))])
      (hyt0 i k)
  refine le_trans ?_ hA
  -- Step B: per-product comparison
  set X := G - L * Mx - pbar - cbar with hX
  set X' := pbar + cbar + G - L * Mx - L with hX'
  have hper : ∀ i, (if ∑ k, C i k = 0 then -(b i * X') else (bt i - b i) * X) ≤
      bt i * Y i - b i * Z i := by
    intro i
    by_cases hid : ∑ k, C i k = 0
    · rw [if_pos hid, hbt_hid i hid, zero_mul, zero_sub, neg_le_neg_iff]
      rcases (hb_nn i).lt_or_eq with hbi | hbi
      · refine mul_le_mul_of_nonneg_left ?_ (hb_nn i)
        have hy1 := hyt1 i hbi
        simp only [hZ]
        have : (∑ k, yt i k * (G - L * Ψe i k - Q.c i j k)) ≤
            ∑ k, yt i k * (G - L * (Mx + 1) + cbar) := by
          refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (hyt0 i k)
          have := hMxe i hid k
          have := (abs_le.1 (hc i k)).1
          nlinarith
        rw [← Finset.sum_mul, hy1, one_mul] at this
        have := (abs_le.1 (hp i (φ i))).2
        simp only [hX']
        linarith
      · rw [← hbi]; simp
    · rw [if_neg hid]
      rcases (hb_nn i).lt_or_eq with hbi | hbi
      · have hy1 := hyt1 i hbi
        have hYZ : Z i ≤ Y i := by
          simp only [hY, hZ, hφt_ne i hid]
          refine (add_le_add_iff_left _).2 (Finset.sum_le_sum fun k _ => ?_)
          refine mul_le_mul_of_nonneg_left ?_ (hyt0 i k)
          by_cases hck : 0 < C i k
          · rw [fc_of_pos Q C j i k hck]
            have := h1 i k hck
            nlinarith
          · have hck0 : C i k = 0 := by omega
            have hpos := fc_pos Q C j i k hid
            have := h2 i k hck0 i (Q.fcChoice C j i k) hpos
            have := (abs_le.1 (hc i k)).1
            have := (abs_le.1 (hc i (Q.fcChoice C j i k))).2
            nlinarith
        have hYlow : X ≤ Y i := by
          simp only [hY, hX]
          have : (∑ k, yt i k * (G - L * Mx - cbar)) ≤ ∑ k, yt i k *
              (G - L * Ψ (Q.take C i (Q.fcChoice C j i k)) - Q.c i j (Q.fcChoice C j i k)) := by
            refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (hyt0 i k)
            have hpos := fc_pos Q C j i k hid
            have := hMxT i _ hpos
            have := (abs_le.1 (hc i (Q.fcChoice C j i k))).2
            nlinarith
          rw [← Finset.sum_mul, hy1, one_mul] at this
          have := (abs_le.1 (hp i (φt i))).1
          linarith
        have hge := hbt_ge i hid
        nlinarith [mul_le_mul_of_nonneg_left hYZ (hb_nn i),
          mul_le_mul_of_nonneg_left hYlow (by linarith : 0 ≤ bt i - b i)]
      · rw [← hbi, hb0 i hbi.symm]; simp
  -- Step C: combine
  have hsumper := Finset.sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin Q.I))) => hper i
  set σ := ∑ i, (if ∑ k, C i k = 0 then 0 else bt i - b i) with hσ
  set mS := ∑ i, (if ∑ k, C i k = 0 then b i else 0) with hmS
  have hsplit : (∑ i, (if ∑ k, C i k = 0 then -(b i * X') else (bt i - b i) * X)) =
      σ * X - mS * X' := by
    simp only [hσ, hmS, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  have hdiff : ∑ i, b i - ∑ i, bt i = mS - σ := by
    simp only [hσ, hmS, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · simp [hbt_hid i h]
    · ring
  have hσ0 : 0 ≤ σ := Finset.sum_nonneg fun i _ => by
    split_ifs with h
    · exact le_rfl
    · linarith [hbt_ge i h]
  have hσm : σ ≤ mS := by linarith
  rw [hsplit] at hsumper
  rw [Finset.sum_sub_distrib] at hsumper
  have hΨ : (mS - σ) * (G - L * Mx) ≤ (mS - σ) * (G - L * Ψ C) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
  have hfin : 0 ≤ σ * X - mS * X' + (mS - σ) * (G - L * Mx) := by
    simp only [hX, hX']
    nlinarith
  have hkey : (∑ i, b i * Z i) - (∑ i, bt i * Y i) ≤
      ((∑ i, b i) - (∑ i, bt i)) * (G - L * Ψ C) := by
    rw [hdiff]; linarith
  calc _ ≤ (∑ i, bt i * Y i) + ((∑ i, b i) - (∑ i, bt i)) * (G - L * Ψ C) +
        (1 - ∑ i, b i) * (G - L * Ψ C) := by linarith
    _ = _ := by ring


end S2

section S3

lemma vnn (P : Inst) (hP : P.Standing) : ∀ i j r, 0 ≤ P.v i j r := by
  obtain ⟨-, -, -, -, -, -, hvpos, hv0, -, -⟩ := hP
  intro i j r
  by_cases h : r = P.noDisp
  · rw [h, hv0]
  · exact (hvpos i j r h).le

lemma rhoTil_nonneg {I R : ℕ} {x : Fin I → Fin R → ℝ} (d : FramingDecomp x)
    (φ : Fin I → Fin R) : 0 ≤ rhoTil d φ := by
  classical
  unfold rhoTil
  refine Finset.sum_nonneg fun l _ => ?_
  split_ifs
  · exact (d.isDecomp.1 l).1.le
  · exact le_rfl

lemma rho_nonneg (P : Inst) (hP : P.Standing) (j : Fin P.J) {x : Fin P.I → Fin P.R → ℝ}
    (d : FramingDecomp x) (φ : Fin P.I → Fin P.R) : 0 ≤ P.rho j d φ := by
  unfold Inst.rho
  split_ifs
  · refine div_nonneg (mul_nonneg (rhoTil_nonneg d φ) ?_) ?_
    · have : 0 ≤ ∑ i, P.vPhi j φ i := Finset.sum_nonneg fun i _ => vnn P hP _ _ _
      linarith
    · have : 0 ≤ ∑ φ' ∈ P.Omega, rhoTil d φ' * ∑ i, P.vPhi j φ' i :=
        Finset.sum_nonneg fun φ' _ => mul_nonneg (rhoTil_nonneg d φ')
          (Finset.sum_nonneg fun i _ => vnn P hP _ _ _)
      linarith
  · exact le_rfl

/-- If `ρ(φ) > 0` then every coordinate of `φ` carries positive mass in `x`. -/
lemma x_pos_of_rho_pos (P : Inst) (j : Fin P.J) {x : Fin P.I → Fin P.R → ℝ}
    (d : FramingDecomp x) (φ : Fin P.I → Fin P.R) (h : 0 < P.rho j d φ) (i : Fin P.I) :
    0 < x i (φ i) := by
  classical
  have hrt : 0 < rhoTil d φ := by
    unfold Inst.rho at h
    split_ifs at h with hm
    · by_contra hc
      push Not at hc
      have h0 : rhoTil d φ = 0 := le_antisymm hc (rhoTil_nonneg d φ)
      rw [h0] at h; simp at h
    · exact absurd h (lt_irrefl 0)
  unfold rhoTil at hrt
  obtain ⟨l, -, hl⟩ := Finset.exists_lt_of_sum_lt (s := univ)
    (f := fun _ => (0:ℝ)) (by simpa using hrt)
  have hc : ∀ i r, φ i = r ↔ d.B l (Fin.castAdd (Itil x) i) r = 1 := by
    by_contra hc
    rw [if_neg hc] at hl
    exact lt_irrefl _ hl
  obtain ⟨hα, -, hBl, hrep⟩ := d.isDecomp
  have hx := hrep (Fin.castAdd (Itil x) i) (φ i)
  simp only [Bmat, Fin.addCases_left] at hx
  rw [hx]
  have hnn : ∀ l', 0 ≤ d.α l' * d.B l' (Fin.castAdd (Itil x) i) (φ i) := by
    intro l'
    refine mul_nonneg (hα l').1.le ?_
    rcases (hBl l').1 (Fin.castAdd (Itil x) i) (φ i) with h | h <;> rw [h] <;> norm_num
  calc (0:ℝ) < d.α l * d.B l (Fin.castAdd (Itil x) i) (φ i) := by
        rw [(hc i (φ i)).1 rfl, mul_one]; exact (hα l).1
    _ ≤ _ := Finset.single_le_sum (fun l' _ => hnn l') (Finset.mem_univ l)


noncomputable def qy (Q : Inst) (s : DETSol Q) : Fin Q.T → Fin Q.I → Fin Q.K → ℝ :=
  fun t i k => ∑ j, s.y t j i k

noncomputable def perT (Q : Inst) (s : DETSol Q) (t : Fin Q.T) : ℝ :=
  (∑ i, ∑ j, Q.revX j (s.x t j) i) - ∑ j, ∑ i, ∑ k, Q.c i j k * s.y t j i k

noncomputable def Gs (Q : Inst) (s : DETSol Q) (n : ℕ) : ℝ :=
  ∑ t : Fin Q.T, if Q.T - n ≤ t.val then perT Q s t else 0

noncomputable def pbar (Q : Inst) : ℝ := ∑ i, ∑ r, |Q.p i r|
noncomputable def cbar (Q : Inst) : ℝ := ∑ i, ∑ j, ∑ k, |Q.c i j k|
noncomputable def Lc (Q : Inst) : ℝ := 2 * (pbar Q + cbar Q)

lemma tail_succ {T : ℕ} (f : Fin T → ℝ) (n : ℕ) (h : n + 1 ≤ T) :
    (∑ t : Fin T, if T - (n + 1) ≤ t.val then f t else 0) =
      f ⟨T - (n + 1), by omega⟩ + ∑ t : Fin T, if T - n ≤ t.val then f t else 0 := by
  set t0 : Fin T := ⟨T - (n + 1), by omega⟩
  calc (∑ t : Fin T, if T - (n + 1) ≤ t.val then f t else 0) =
      ∑ t : Fin T, ((if t0 = t then f t else 0) + (if T - n ≤ t.val then f t else 0)) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases h1 : t0 = t
        · subst h1
          simp only [t0, if_true, le_refl, show ¬ (T - n ≤ T - (n + 1)) by omega, if_false,
            add_zero]
        · have h2 : t.val ≠ T - (n + 1) := fun h' => h1 (Fin.ext h'.symm)
          by_cases h3 : T - n ≤ t.val
          · rw [if_pos (by omega), if_neg h1, if_pos h3, zero_add]
          · rw [if_neg (by omega), if_neg h1, if_neg h3, add_zero]
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_ite_eq]; simp

lemma Gs_succ (Q : Inst) (s : DETSol Q) (n : ℕ) (h : n + 1 ≤ Q.T) :
    Gs Q s (n + 1) = perT Q s ⟨Q.T - (n + 1), by omega⟩ + Gs Q s n :=
  tail_succ (perT Q s) n h

lemma Gs_zero (Q : Inst) (s : DETSol Q) : Gs Q s 0 = 0 := by
  unfold Gs
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [if_neg]; have := t.2; omega

lemma Gs_T (Q : Inst) (s : DETSol Q) : Gs Q s Q.T = Q.detObj s := by
  unfold Gs Inst.detObj
  simp only [Nat.sub_self, zero_le, if_true]
  simp only [perT, Finset.sum_sub_distrib]

lemma swap3' {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℝ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c := by
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]

lemma thetaPhi_eq (Q : Inst) (j : Fin Q.J) (φ : Fin Q.I → Fin Q.R) (i : Fin Q.I) :
    Q.thetaPhi j φ i = Q.lam j * Q.buyProb j φ i := by
  simp only [Inst.thetaPhi, Inst.buyProb, mul_div_assoc]

lemma revPhi_eq (Q : Inst) (j : Fin Q.J) (φ : Fin Q.I → Fin Q.R) (i : Fin Q.I) :
    Q.revPhi j φ i = Q.lam j * Q.buyProb j φ i * Q.p i (φ i) := by
  simp only [Inst.revPhi, Inst.buyProb, Inst.vPhi]; ring

lemma pbar_ge (Q : Inst) (i : Fin Q.I) (r : Fin Q.R) : |Q.p i r| ≤ pbar Q := by
  unfold pbar
  calc |Q.p i r| ≤ ∑ r', |Q.p i r'| :=
        Finset.single_le_sum (f := fun r' => |Q.p i r'|) (fun _ _ => abs_nonneg _) (mem_univ r)
    _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ r', |Q.p i' r'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (mem_univ i)

lemma cbar_ge (Q : Inst) (i : Fin Q.I) (j : Fin Q.J) (k : Fin Q.K) : |Q.c i j k| ≤ cbar Q := by
  unfold cbar
  calc |Q.c i j k| ≤ ∑ k', |Q.c i j k'| :=
        Finset.single_le_sum (f := fun k' => |Q.c i j k'|) (fun _ _ => abs_nonneg _) (mem_univ k)
    _ ≤ ∑ j', ∑ k', |Q.c i j' k'| := Finset.single_le_sum (f := fun j' => ∑ k', |Q.c i j' k'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j', ∑ k', |Q.c i' j' k'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (mem_univ i)

lemma pbar_nonneg (Q : Inst) : 0 ≤ pbar Q :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma cbar_nonneg (Q : Inst) : 0 ≤ cbar Q :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma qy_facts (Q : Inst) (hQ : Q.Standing) (s : DETSol Q) (hs : s ∈ Q.DETFeasible) :
    (∀ t i k, 0 ≤ qy Q s t i k) ∧ (∀ t, ∑ i, ∑ k, qy Q s t i k ≤ 1) := by
  obtain ⟨-, -, h10c, -, h10e, h10f⟩ := hs
  have hv := vnn Q hQ
  obtain ⟨-, -, -, -, hlam, hlamsum, -, -, -, -⟩ := hQ
  refine ⟨fun t i k => Finset.sum_nonneg fun j _ => (h10f t j i k).1, fun t => ?_⟩
  have hj : ∀ j, ∑ i, Q.thetaX j (s.x t j) i ≤ Q.lam j := by
    intro j
    simp only [Inst.thetaX]
    rw [← Finset.sum_div]
    have hD : 0 ≤ ∑ l, ∑ r, Q.v l j r * s.x t j l r :=
      Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun r _ =>
        mul_nonneg (hv _ _ _) (h10e t j l r).1
    rw [div_le_iff₀ (by linarith), ← Finset.mul_sum]
    nlinarith [(hlam j).1]
  calc (∑ i, ∑ k, qy Q s t i k) = ∑ j, ∑ i, Q.thetaX j (s.x t j) i := by
        simp only [qy]
        rw [swap3']
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => h10c t j i
    _ ≤ ∑ j, Q.lam j := Finset.sum_le_sum fun j _ => hj j
    _ ≤ 1 := hlamsum

lemma ytil_mul (Q : Inst) (s : DETSol Q) (hs : s ∈ Q.DETFeasible) (t : Fin Q.T) (j : Fin Q.J)
    (i : Fin Q.I) (k : Fin Q.K) :
    Q.thetaX j (s.x t j) i * Q.ytil (s.y t j) i k = s.y t j i k := by
  obtain ⟨-, -, h10c, -, -, h10f⟩ := hs
  rw [← h10c t j i]
  unfold Inst.ytil
  by_cases h0 : ∑ k', s.y t j i k' = 0
  · rw [h0, zero_mul]
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k' _ => (h10f t j i k').1)).1 h0 k
      (mem_univ k)
    rw [this]
  · field_simp

lemma PJ (Q : Inst) (hQ : Q.Standing) (s : DETSol Q) (hs : s ∈ Q.DETFeasible) (t : Fin Q.T)
    (j : Fin Q.J) (d : FramingDecomp (s.x t j)) (G L Ψ0 : ℝ) (Ψe : Fin Q.I → Fin Q.K → ℝ) :
    Q.lam j * ∑ φ ∈ Q.Omega, Q.rho j d φ *
      ((∑ i, Q.buyProb j φ i * (Q.p i (φ i) +
          ∑ k, Q.ytil (s.y t j) i k * (G - L * Ψe i k - Q.c i j k))) +
        (1 - ∑ i, Q.buyProb j φ i) * (G - L * Ψ0)) =
    ∑ i, Q.revX j (s.x t j) i + ∑ i, ∑ k, s.y t j i k * (G - L * Ψe i k - Q.c i j k) +
      (Q.lam j - ∑ i, ∑ k, s.y t j i k) * (G - L * Ψ0) := by
  have hs' := hs
  obtain ⟨h10a, h10b, h10c, -, h10e, -⟩ := hs'
  obtain ⟨ha, hb, hc⟩ := FramingFulfillment.RFF.lemma_3 Q hQ j (s.x t j) (h10a t j) (h10b t j)
    (h10e t j) d
  set S : Fin Q.I → ℝ := fun i => ∑ k, Q.ytil (s.y t j) i k * (G - L * Ψe i k - Q.c i j k)
    with hS
  set W0 := G - L * Ψ0
  have e1 : ∀ φ, Q.lam j * (Q.rho j d φ * ((∑ i, Q.buyProb j φ i * (Q.p i (φ i) + S i)) +
      (1 - ∑ i, Q.buyProb j φ i) * W0)) =
      ∑ i, Q.rho j d φ * Q.revPhi j φ i + ∑ i, Q.rho j d φ * Q.thetaPhi j φ i * S i +
        Q.rho j d φ * Q.lam j * W0 - ∑ i, Q.rho j d φ * Q.thetaPhi j φ i * W0 := by
    intro φ
    simp only [revPhi_eq, thetaPhi_eq]
    have h1 : (∑ i, Q.buyProb j φ i * (Q.p i (φ i) + S i)) =
        ∑ i, Q.buyProb j φ i * Q.p i (φ i) + ∑ i, Q.buyProb j φ i * S i := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1]
    have h2 : (∑ i, Q.rho j d φ * (Q.lam j * Q.buyProb j φ i * Q.p i (φ i))) =
        Q.rho j d φ * Q.lam j * ∑ i, Q.buyProb j φ i * Q.p i (φ i) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    have h3 : (∑ i, Q.rho j d φ * (Q.lam j * Q.buyProb j φ i) * S i) =
        Q.rho j d φ * Q.lam j * ∑ i, Q.buyProb j φ i * S i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    have h4 : (∑ i, Q.rho j d φ * (Q.lam j * Q.buyProb j φ i) * W0) =
        Q.rho j d φ * Q.lam j * (∑ i, Q.buyProb j φ i) * W0 := by
      rw [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2, h3, h4]; ring
  rw [Finset.mul_sum, Finset.sum_congr rfl fun φ _ => e1 φ]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun φ i => Q.rho j d φ * Q.revPhi j φ i),
    Finset.sum_comm (f := fun φ i => Q.rho j d φ * Q.thetaPhi j φ i * S i),
    Finset.sum_comm (f := fun φ i => Q.rho j d φ * Q.thetaPhi j φ i * W0)]
  have e2 : ∀ i, (∑ φ ∈ Q.Omega, Q.rho j d φ * Q.thetaPhi j φ i * S i) =
      Q.thetaX j (s.x t j) i * S i := by
    intro i; rw [← Finset.sum_mul, hb i]
  have e3 : ∀ i, (∑ φ ∈ Q.Omega, Q.rho j d φ * Q.thetaPhi j φ i * W0) =
      Q.thetaX j (s.x t j) i * W0 := by
    intro i; rw [← Finset.sum_mul, hb i]
  have e4 : (∑ φ ∈ Q.Omega, Q.rho j d φ * Q.lam j * W0) = Q.lam j * W0 := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, ha, one_mul]
  simp only [hc, e2, e3, e4]
  have e5 : ∀ i, Q.thetaX j (s.x t j) i * S i =
      ∑ k, s.y t j i k * (G - L * Ψe i k - Q.c i j k) := by
    intro i
    simp only [hS, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, ytil_mul Q s hs t j i k]
  simp only [e5]
  have e6 : (∑ i, Q.thetaX j (s.x t j) i * W0) = (∑ i, ∑ k, s.y t j i k) * W0 := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by rw [h10c t j i]
  rw [e6]; ring

lemma succ_core (Q : Inst) (hQ : Q.Standing) (s : DETSol Q) (hs : s ∈ Q.DETFeasible)
    (dec : ∀ (t : Fin Q.T) (j : Fin Q.J), FramingDecomp (s.x t j)) (n : ℕ) (hn : n + 1 ≤ Q.T)
    (C : Q.Inv) (G : ℝ) (R Ψ : Q.Inv → ℝ) (Ψe : Fin Q.I → Fin Q.K → ℝ)
    (hR : ∀ C', G - Lc Q * Ψ C' ≤ R C')
    (h1 : ∀ i k, 0 < C i k → Ψ (Q.take C i k) ≤ Ψe i k)
    (h2 : ∀ i k, C i k = 0 → ∀ i' k', 0 < C i' k' → Ψ (Q.take C i' k') + 1 ≤ Ψe i k)
    (h3 : ∀ i k, C i k = 0 → Ψ C + 1 ≤ Ψe i k) :
    perT Q s ⟨Q.T - (n + 1), by omega⟩ + G - Lc Q *
      ((1 - ∑ i, ∑ k, qy Q s ⟨Q.T - (n + 1), by omega⟩ i k) * Ψ C +
        ∑ i, ∑ k, qy Q s ⟨Q.T - (n + 1), by omega⟩ i k * Ψe i k) ≤
    (1 - ∑ j, Q.lam j) * R C +
      ∑ j, Q.lam j * ∑ φ ∈ Q.Omega, Q.rho j (dec ⟨Q.T - (n + 1), by omega⟩ j) φ *
        ((∑ i, Q.buyProb j (Q.hideOut C φ) i *
            (Q.p i (Q.hideOut C φ i) +
              ∑ k, Q.ytil (s.y ⟨Q.T - (n + 1), by omega⟩ j) i k *
                (R (Q.take C i (Q.fcChoice C j i k)) - Q.c i j (Q.fcChoice C j i k)))) +
         (1 - ∑ i, Q.buyProb j (Q.hideOut C φ) i) * R C) := by
  classical
  set t : Fin Q.T := ⟨Q.T - (n + 1), by omega⟩ with ht
  have hv := vnn Q hQ
  have hQ' := hQ
  obtain ⟨hI, -, hK, -, hlam, hlamsum, hvpos, hv0, -, -⟩ := hQ'
  have hs' := hs
  obtain ⟨h10a, h10b, h10c, -, h10e, h10f⟩ := hs'
  set L := Lc Q with hLdef
  -- the bound `Mx` on continuation potentials
  have hne : (univ : Finset (Fin Q.I × Fin Q.K)).Nonempty := ⟨(⟨0, hI⟩, ⟨0, hK⟩), mem_univ _⟩
  let M0 : Fin Q.I × Fin Q.K → ℝ := fun pk =>
    if 0 < C pk.1 pk.2 then Ψ (Q.take C pk.1 pk.2) else Ψ C
  set Mx := max (Ψ C) (univ.sup' hne M0) with hMx
  have hMxC : Ψ C ≤ Mx := le_max_left _ _
  have hMxT : ∀ i k, 0 < C i k → Ψ (Q.take C i k) ≤ Mx := by
    intro i k h
    have : M0 (i, k) = Ψ (Q.take C i k) := by simp only [M0, if_pos h]
    rw [← this]
    exact le_trans (Finset.le_sup' M0 (mem_univ (i, k))) (le_max_right _ _)
  have hMxe : ∀ i, ∑ k, C i k = 0 → ∀ k, Mx + 1 ≤ Ψe i k := by
    intro i hi k
    have hCk : C i k = 0 := (Finset.sum_eq_zero_iff.1 hi) k (mem_univ k)
    have : Mx ≤ Ψe i k - 1 := by
      refine max_le (by linarith [h3 i k hCk]) (Finset.sup'_le _ _ fun pk _ => ?_)
      simp only [M0]
      split_ifs with hpk
      · linarith [h2 i k hCk pk.1 pk.2 hpk]
      · linarith [h3 i k hCk]
    linarith
  -- per region comparison
  have hjle : ∀ j, Q.lam j * ∑ φ ∈ Q.Omega, Q.rho j (dec t j) φ *
      ((∑ i, Q.buyProb j φ i * (Q.p i (φ i) +
          ∑ k, Q.ytil (s.y t j) i k * (G - L * Ψe i k - Q.c i j k))) +
        (1 - ∑ i, Q.buyProb j φ i) * (G - L * Ψ C)) ≤
      Q.lam j * ∑ φ ∈ Q.Omega, Q.rho j (dec t j) φ *
        ((∑ i, Q.buyProb j (Q.hideOut C φ) i *
            (Q.p i (Q.hideOut C φ i) +
              ∑ k, Q.ytil (s.y t j) i k *
                (R (Q.take C i (Q.fcChoice C j i k)) - Q.c i j (Q.fcChoice C j i k)))) +
         (1 - ∑ i, Q.buyProb j (Q.hideOut C φ) i) * R C) := by
    intro j
    rcases (hlam j).1.lt_or_eq with hlj | hlj
    swap
    · rw [← hlj]; simp
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun φ hφ => ?_) (hlam j).1
    rcases (rho_nonneg Q hQ j (dec t j) φ).lt_or_eq with hρ | hρ
    swap
    · rw [← hρ]; simp
    refine mul_le_mul_of_nonneg_left ?_ hρ.le
    have hyt1 : ∀ i, 0 < Q.buyProb j φ i → ∑ k, Q.ytil (s.y t j) i k = 1 := by
      intro i hb
      have hx := x_pos_of_rho_pos Q j (dec t j) φ hρ i
      have hvp : 0 < Q.v i j (φ i) := by
        rcases (hv i j (φ i)).lt_or_eq with h | h
        · exact h
        · exfalso
          simp only [Inst.buyProb, Inst.vPhi, ← h, zero_div] at hb
          exact lt_irrefl _ hb
      have hypos : 0 < ∑ k, s.y t j i k := by
        rw [h10c t j i]
        unfold Inst.thetaX
        refine div_pos (mul_pos hlj ?_) ?_
        · calc (0:ℝ) < Q.v i j (φ i) * s.x t j i (φ i) := mul_pos hvp hx
            _ ≤ _ := Finset.single_le_sum (f := fun r => Q.v i j r * s.x t j i r)
                (fun r _ => mul_nonneg (hv _ _ _) (h10e t j i r).1) (Finset.mem_univ _)
        · have : 0 ≤ ∑ l, ∑ r, Q.v l j r * s.x t j l r :=
            Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun r _ =>
              mul_nonneg (hv _ _ _) (h10e t j l r).1
          linarith
      unfold Inst.ytil; rw [← Finset.sum_div, div_self hypos.ne']
    have hyt0 : ∀ i k, 0 ≤ Q.ytil (s.y t j) i k := fun i k =>
      div_nonneg (h10f t j i k).1 (Finset.sum_nonneg fun k' _ => (h10f t j i k').1)
    exact step Q hv hv0 C j φ (Q.ytil (s.y t j)) hyt0 hyt1 R Ψ Ψe G L (pbar Q) (cbar Q) Mx
      hR h1 h2 hMxC hMxT hMxe (pbar_ge Q) (fun i k => cbar_ge Q i j k) (pbar_nonneg Q)
      (cbar_nonneg Q) (by simp only [hLdef, Lc]; exact le_rfl)
  have h0le : (1 - ∑ j, Q.lam j) * (G - L * Ψ C) ≤ (1 - ∑ j, Q.lam j) * R C :=
    mul_le_mul_of_nonneg_left (hR C) (by linarith)
  refine le_trans (le_of_eq ?_) (add_le_add h0le (Finset.sum_le_sum fun j _ => hjle j))
  -- the nominal identity
  rw [Finset.sum_congr rfl fun j _ => PJ Q hQ s hs t j (dec t j) G L (Ψ C) Ψe]
  set W0 := G - L * Ψ C
  have eRev : (∑ j, ∑ i, Q.revX j (s.x t j) i) = ∑ i, ∑ j, Q.revX j (s.x t j) i :=
    Finset.sum_comm
  have eY : (∑ i, ∑ k, qy Q s t i k) = ∑ j, ∑ i, ∑ k, s.y t j i k := by
    simp only [qy]; rw [swap3']
  have eYΨ : (∑ i, ∑ k, qy Q s t i k * Ψe i k) = ∑ j, ∑ i, ∑ k, s.y t j i k * Ψe i k := by
    simp only [qy, Finset.sum_mul]; rw [swap3']
  have eW : (∑ j, ∑ i, ∑ k, s.y t j i k * (G - L * Ψe i k - Q.c i j k)) =
      G * (∑ j, ∑ i, ∑ k, s.y t j i k) - L * (∑ j, ∑ i, ∑ k, s.y t j i k * Ψe i k) -
        ∑ j, ∑ i, ∑ k, Q.c i j k * s.y t j i k := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun k _ => by ring
  have eL : (∑ j, (Q.lam j - ∑ i, ∑ k, s.y t j i k) * W0) =
      (∑ j, Q.lam j) * W0 - (∑ j, ∑ i, ∑ k, s.y t j i k) * W0 := by
    rw [← sub_mul, ← Finset.sum_sub_distrib, Finset.sum_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, eL, eW, eRev]
  simp only [perT]
  rw [eY, eYΨ]
  ring

theorem lower (Q : Inst) (hQ : Q.Standing) (s : DETSol Q) (hs : s ∈ Q.DETFeasible)
    (dec : ∀ (t : Fin Q.T) (j : Fin Q.J), FramingDecomp (s.x t j)) :
    ∀ n, n ≤ Q.T → ∀ C : Q.Inv,
      Gs Q s n - Lc Q * Ex Q (qy Q s) n (pot Q C) ≤ Q.rffValue s dec n C := by
  obtain ⟨hq0, hq1⟩ := qy_facts Q hQ s hs
  have hL0 : 0 ≤ Lc Q := by
    unfold Lc; linarith [pbar_nonneg Q, cbar_nonneg Q]
  intro n
  induction n with
  | zero =>
    intro _ C
    rw [Gs_zero]
    simp only [Ex, Inst.rffValue]
    nlinarith [pot_nonneg Q C 0]
  | succ n ih =>
    intro hn C
    have ihn := ih (by omega)
    rw [Inst.rffValue, dif_pos hn, Gs_succ Q s n hn, Ex_succ (qy Q s) n hn]
    refine succ_core Q hQ s hs dec n hn C (Gs Q s n) (Q.rffValue s dec n)
      (fun C' => Ex Q (qy Q s) n (pot Q C'))
      (fun i k => Ex Q (qy Q s) n (fun N => pot Q C (addE Q N i k))) ihn ?_ ?_ ?_
    · intro i k h
      exact Ex_mono (qy Q s) hq0 hq1 n _ _ fun N => pot_serve Q C N i k h
    · intro i k h i' k' h'
      have e := Ex_add (qy Q s) n (pot Q (Q.take C i' k')) (fun _ => (1:ℝ))
      rw [Ex_const] at e
      show Ex Q (qy Q s) n (pot Q (Q.take C i' k')) + 1 ≤ _
      rw [← e]
      exact Ex_mono (qy Q s) hq0 hq1 n _ _ fun N => pot_hit_reroute Q C N i k h i' k' h'
    · intro i k h
      have e := Ex_add (qy Q s) n (pot Q C) (fun _ => (1:ℝ))
      rw [Ex_const] at e
      show Ex Q (qy Q s) n (pot Q C) + 1 ≤ _
      rw [← e]
      exact Ex_mono (qy Q s) hq0 hq1 n _ _ fun N => pot_hit_none Q C N i k h

theorem gap_general (Q : Inst) (hQ : Q.Standing) (s : DETSol Q) (hs : s ∈ Q.DETFeasible)
    (dec : ∀ (t : Fin Q.T) (j : Fin Q.J), FramingDecomp (s.x t j)) :
    Q.detObj s - Q.JRFF s dec ≤
      Lc Q * ((2 * ((Q.I * Q.K : ℕ) : ℝ) + 2) * (((Q.I * Q.K : ℕ) : ℝ) * Real.sqrt Q.T)) := by
  obtain ⟨hq0, hq1⟩ := qy_facts Q hQ s hs
  have hs' := hs
  obtain ⟨-, -, -, h10d, -, -⟩ := hs'
  have hL0 : 0 ≤ Lc Q := by
    unfold Lc; linarith [pbar_nonneg Q, cbar_nonneg Q]
  have hlow := lower Q hQ s hs dec Q.T le_rfl Q.C
  rw [Gs_T] at hlow
  have hJ : Q.JRFF s dec = Q.rffValue s dec Q.T Q.C := rfl
  rw [hJ]
  -- bound the potential
  have hpot : Ex Q (qy Q s) Q.T (pot Q Q.C) ≤
      (2 * ((Q.I * Q.K : ℕ) : ℝ) + 2) * (((Q.I * Q.K : ℕ) : ℝ) * Real.sqrt Q.T) := by
    calc Ex Q (qy Q s) Q.T (pot Q Q.C) ≤ Ex Q (qy Q s) Q.T (fun N =>
          (2 * ((Q.I * Q.K : ℕ) : ℝ) + 2) *
            ∑ p : Fin Q.I × Fin Q.K, max 0 ((N p.1 p.2 : ℝ) - (Q.C p.1 p.2 : ℝ))) :=
          Ex_mono (qy Q s) hq0 hq1 _ _ _ fun N => pot_le Q Q.C N
      _ = (2 * ((Q.I * Q.K : ℕ) : ℝ) + 2) * ∑ p : Fin Q.I × Fin Q.K,
            Ex Q (qy Q s) Q.T (fun N => max 0 ((N p.1 p.2 : ℝ) - (Q.C p.1 p.2 : ℝ))) := by
          rw [Ex_smul, Ex_sum]
      _ ≤ (2 * ((Q.I * Q.K : ℕ) : ℝ) + 2) * ∑ _p : Fin Q.I × Fin Q.K, Real.sqrt Q.T := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => ?_) (by positivity)
          have hmu : mu (qy Q s) p.1 p.2 Q.T = ∑ t, ∑ j, s.y t j p.1 p.2 := by
            unfold mu qy; simp
          have hmuC : mu (qy Q s) p.1 p.2 Q.T ≤ (Q.C p.1 p.2 : ℝ) := by
            rw [hmu]; exact h10d p.1 p.2
          have hmuT : mu (qy Q s) p.1 p.2 Q.T ≤ Q.T := by
            unfold mu
            calc _ ≤ ∑ _t : Fin Q.T, (1:ℝ) := Finset.sum_le_sum fun t _ => by
                  split_ifs
                  · calc qy Q s t p.1 p.2 ≤ ∑ k, qy Q s t p.1 k :=
                          Finset.single_le_sum (f := fun k => qy Q s t p.1 k)
                            (fun k _ => hq0 _ _ _) (mem_univ _)
                      _ ≤ ∑ i, ∑ k, qy Q s t i k :=
                          Finset.single_le_sum (f := fun i => ∑ k, qy Q s t i k)
                            (fun i _ => Finset.sum_nonneg fun k _ => hq0 _ _ _) (mem_univ _)
                      _ ≤ 1 := hq1 t
                  · norm_num
              _ = Q.T := by simp
          exact le_trans (Ex_excess_le (qy Q s) hq0 hq1 p.1 p.2 _ hmuC)
            (Real.sqrt_le_sqrt hmuT)
      _ = _ := by simp
  nlinarith [mul_le_mul_of_nonneg_left hpot hL0]


end S3

lemma JD_eq (Q : Inst) (s : DETSol Q) (hs : Q.IsDETOpt s) : Q.JD = Q.detObj s :=
  IsGreatest.csSup_eq ⟨⟨s, hs.1, rfl⟩, by rintro _ ⟨s', hs', rfl⟩; exact hs.2 s' hs'⟩

end RFFGap

open RFFGap

theorem solution (P : Inst) (hP : P.Standing) :
    ∃ M : ℝ, 0 < M ∧ ∃ θ₀ : ℕ, ∀ θ : ℕ, θ₀ ≤ θ →
      ∀ s, (P.scale θ).IsDETOpt s →
        ∀ dec : ∀ (t : Fin (P.scale θ).T) (j : Fin (P.scale θ).J), FramingDecomp (s.x t j),
          (P.scale θ).JD - (P.scale θ).JRFF s dec ≤ M * Real.sqrt (θ : ℝ) := by
  set K0 := Lc P * ((2 * ((P.I * P.K : ℕ) : ℝ) + 2) * (((P.I * P.K : ℕ) : ℝ) * Real.sqrt P.T))
    with hK0
  have hK0nn : 0 ≤ K0 := by
    have : 0 ≤ Lc P := by unfold Lc; linarith [pbar_nonneg P, cbar_nonneg P]
    positivity
  refine ⟨K0 + 1, by linarith, 0, fun θ _ s hs dec => ?_⟩
  have hS : (P.scale θ).Standing := hP
  have h := gap_general (P.scale θ) hS s hs.1 dec
  rw [← JD_eq _ s hs] at h
  have hT : ((P.scale θ).T : ℝ) = (θ : ℝ) * P.T := by
    show (((θ * P.T : ℕ)) : ℝ) = _; push_cast; ring
  rw [hT, Real.sqrt_mul (Nat.cast_nonneg _)] at h
  have hθ : 0 ≤ Real.sqrt (θ : ℝ) := Real.sqrt_nonneg _
  have e : Lc (P.scale θ) * ((2 * (((P.scale θ).I * (P.scale θ).K : ℕ) : ℝ) + 2) *
      ((((P.scale θ).I * (P.scale θ).K : ℕ) : ℝ) * (Real.sqrt θ * Real.sqrt P.T))) =
      K0 * Real.sqrt θ := by
    have e1 : Lc (P.scale θ) = Lc P := rfl
    have e2 : (P.scale θ).I * (P.scale θ).K = P.I * P.K := rfl
    rw [e1, e2, hK0]; ring
  rw [e] at h
  nlinarith
