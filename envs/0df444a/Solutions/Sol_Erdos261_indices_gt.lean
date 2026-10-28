-- Prove2me | solution 1 for Erdos261.indices_gt
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T18:47:01.964893+00:00
-- url     : https://prove2.me/submissions/9ff7e82c-4716-406b-ab10-bd296d1de335

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset


namespace E261B
open Finset

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

lemma telescope (N : ℕ) (c r : ℕ → ℤ) (hr : ∀ j ∈ Icc 1 N, 2 * r j = c j + r (j + 1)) :
    ∀ k ≤ N, ∑ j ∈ Icc 1 k, c j * 2 ^ (k - j) = r 1 * 2 ^ k - r (k + 1) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    rw [Finset.sum_Icc_succ_top (by omega), Nat.sub_self, pow_zero, mul_one]
    have e : ∑ j ∈ Icc 1 k, c j * 2 ^ (k + 1 - j) = 2 * ∑ j ∈ Icc 1 k, c j * 2 ^ (k - j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_Icc] at hj
      rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ]; ring
    rw [e, ih']
    have := hr (k + 1) (Finset.mem_Icc.2 ⟨by omega, hk⟩)
    rw [pow_succ]
    linarith

/-- A3 (signed binary-carry formulation). For any integer column coefficients `c_1, …, c_N`,
`∑_{j=1}^N c_j 2^{N-j} = 0` iff there are integer carries `r` with `r_{N+1} = 0`, `r_1 = 0` and
`2 r_j = c_j + r_{j+1}` for `1 ≤ j ≤ N`. -/
theorem carry_iff (N : ℕ) (c : ℕ → ℤ) :
    ∑ j ∈ Icc 1 N, c j * 2 ^ (N - j) = 0 ↔
      ∃ r : ℕ → ℤ, r (N + 1) = 0 ∧ r 1 = 0 ∧ ∀ j ∈ Icc 1 N, 2 * r j = c j + r (j + 1) := by
  constructor
  · intro h
    -- forward definition: r 0 = r 1 = 0, r (j+1) = 2 r j - c j
    let r : ℕ → ℤ := fun j => Nat.rec (motive := fun _ => ℤ) 0
      (fun i ri => if i = 0 then 0 else 2 * ri - c i) j
    have r1 : r 1 = 0 := by simp [r]
    have rs : ∀ j, 1 ≤ j → r (j + 1) = 2 * r j - c j := by
      intro j hj
      show (if j = 0 then 0 else 2 * r j - c j) = _
      rw [if_neg (by omega)]
    have hr : ∀ j ∈ Icc 1 N, 2 * r j = c j + r (j + 1) := by
      intro j hj
      rw [rs j (Finset.mem_Icc.1 hj).1]; ring
    refine ⟨r, ?_, r1, hr⟩
    have := telescope N c r hr N le_rfl
    rw [h, r1] at this
    linarith
  · rintro ⟨r, hN, h1, hr⟩
    rw [telescope N c r hr N le_rfl, hN, h1]; ring


/-- A1 (Formal Conjectures form): in any representation `n/2^n = ∑_{k<t} a_k/2^{a_k}` with
`t ≥ 2` distinct positive `a_k`, every index exceeds `n`. -/
theorem indices_gt (n t : ℕ) (ht : 2 ≤ t) (a : Fin t → ℕ) (_hinj : a.Injective) (hpos : 1 ≤ a)
    (hsum : (n : ℚ) / 2 ^ n = ∑ k, (a k : ℚ) / 2 ^ (a k)) : ∀ i, n < a i := by
  have hpos' : ∀ i, 1 ≤ a i := fun i => hpos i
  have hsum' : f n = ∑ k, f (a k) := by simpa [f] using hsum
  intro i
  by_contra hle
  push Not at hle
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

/-- A2 (exact integer identity). For a finite `S ⊆ [1, N]` and `1 ≤ n ≤ N`,
`n/2^n = ∑_{k∈S} k/2^k` iff `∑_{j=1}^N c_j 2^{N-j} = 0`, with `c_j = j·[j∈S] - n·[j=n]`. -/
theorem rep_iff_int (n N : ℕ) (S : Finset ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (hS : S ⊆ Icc 1 N) :
    (n : ℚ) / 2 ^ n = ∑ k ∈ S, (k : ℚ) / 2 ^ k ↔
      ∑ j ∈ Icc 1 N, ((if j ∈ S then (j : ℤ) else 0) - (if j = n then (n : ℤ) else 0)) *
        2 ^ (N - j) = 0 := by
  have e1 : ∑ j ∈ Icc 1 N, ((if j ∈ S then (j : ℤ) else 0) - (if j = n then (n : ℤ) else 0)) *
        2 ^ (N - j) = ∑ k ∈ S, (k : ℤ) * 2 ^ (N - k) - n * 2 ^ (N - n) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 N) (· ∈ S)]
    simp only [sub_mul, Finset.sum_sub_distrib]
    have hf : (Icc 1 N).filter (· ∈ S) = S := by
      ext x; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
    have hA : ∑ x ∈ (Icc 1 N).filter (· ∈ S), (if x ∈ S then (x : ℤ) else 0) * 2 ^ (N - x)
        = ∑ k ∈ S, (k : ℤ) * 2 ^ (N - k) := by
      rw [hf]; exact Finset.sum_congr rfl (fun x hx => by simp [hx])
    have hB : ∑ x ∈ (Icc 1 N).filter (fun x => ¬ x ∈ S), (if x ∈ S then (x : ℤ) else 0) * 2 ^ (N - x)
        = 0 := Finset.sum_eq_zero (fun x hx => by simp [(Finset.mem_filter.1 hx).2])
    have hC : ∑ x ∈ (Icc 1 N).filter (· ∈ S), (if x = n then (n : ℤ) else 0) * 2 ^ (N - x)
        + ∑ x ∈ (Icc 1 N).filter (fun x => ¬ x ∈ S), (if x = n then (n : ℤ) else 0) * 2 ^ (N - x)
        = n * 2 ^ (N - n) := by
      rw [Finset.sum_filter_add_sum_filter_not]
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq']
      simp [Finset.mem_Icc, hn, hnN]
    rw [hA, hB]; linarith
  rw [e1]
  have hpow : ∀ k ≤ N, ((2 : ℚ) ^ (N - k)) = 2 ^ N / 2 ^ k := by
    intro k hk
    rw [eq_div_iff (by positivity), ← pow_add, Nat.sub_add_cancel hk]
  have e2 : ((∑ k ∈ S, (k : ℤ) * 2 ^ (N - k) - n * 2 ^ (N - n) : ℤ) : ℚ)
      = 2 ^ N * (∑ k ∈ S, (k : ℚ) / 2 ^ k - (n : ℚ) / 2 ^ n) := by
    push_cast
    rw [mul_sub, Finset.mul_sum, hpow n hnN]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      rw [hpow k (Finset.mem_Icc.1 (hS hk)).2]; ring
    · ring
  constructor
  · intro h
    have : ((∑ k ∈ S, (k : ℤ) * 2 ^ (N - k) - n * 2 ^ (N - n) : ℤ) : ℚ) = 0 := by
      rw [e2, h, sub_self, mul_zero]
    exact_mod_cast this
  · intro h
    have h' : ((∑ k ∈ S, (k : ℤ) * 2 ^ (N - k) - n * 2 ^ (N - n) : ℤ) : ℚ) = 0 := by
      exact_mod_cast h
    rw [e2] at h'
    have : (2 : ℚ) ^ N ≠ 0 := by positivity
    have := (mul_eq_zero.1 h').resolve_left this
    linarith

/-- A3 corollary (Formal Conjectures form): in any representation with `t ≥ 2` distinct
positive indices, the largest index is even. -/
theorem max_index_even (n t : ℕ) (ht : 2 ≤ t) (a : Fin t → ℕ) (hinj : a.Injective) (hpos : 1 ≤ a)
    (hsum : (n : ℚ) / 2 ^ n = ∑ k, (a k : ℚ) / 2 ^ (a k)) : Even (Finset.univ.sup a) := by
  have hgt := indices_gt n t ht a hinj hpos hsum
  set S := Finset.univ.image a
  set N := Finset.univ.sup a
  have hS' : (n : ℚ) / 2 ^ n = ∑ k ∈ S, (k : ℚ) / 2 ^ k := by
    rw [Finset.sum_image (fun x _ y _ hxy => hinj hxy)]; exact hsum
  have hle : ∀ i, a i ≤ N := fun i => Finset.le_sup (f := a) (Finset.mem_univ i)
  obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin t))
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ a
  have hN0 : N = a i0 := hi0
  have hNS : N ∈ S := by rw [hN0]; exact Finset.mem_image_of_mem a (Finset.mem_univ _)
  have hnN : n < N := by rw [hN0]; exact hgt i0
  have hn : 1 ≤ n ∨ n = 0 := by omega
  rcases hn with hn | hn
  · have hSsub : S ⊆ Icc 1 N := by
      intro k hk
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hk
      exact Finset.mem_Icc.2 ⟨hpos i, hle i⟩
    have h0 := (rep_iff_int n N S hn hnN.le hSsub).1 hS'
    obtain ⟨r, hrN, -, hr⟩ := (carry_iff N _).1 h0
    have := hr N (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩)
    rw [if_pos hNS, if_neg (by omega), hrN] at this
    exact ⟨(r N).toNat, by omega⟩
  · -- n = 0: the left side is 0, impossible for a nonempty sum of positive terms
    exfalso
    subst hn
    have hpos' : ∀ i, (0 : ℚ) < (a i : ℚ) / 2 ^ (a i) := fun i => by
      have : (0 : ℚ) < a i := by exact_mod_cast hpos i
      positivity
    have : (0 : ℚ) < ∑ k, (a k : ℚ) / 2 ^ (a k) :=
      Finset.sum_pos (fun i _ => hpos' i) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    simp at hsum; linarith

end E261B



namespace Erdos261

theorem indices_gt (n t : ℕ) (ht : 2 ≤ t) (a : Fin t → ℕ) (hinj : a.Injective) (hpos : 1 ≤ a)
    (hsum : (n : ℚ) / 2 ^ n = ∑ k, (a k : ℚ) / 2 ^ (a k)) : ∀ i, n < a i :=
  E261B.indices_gt n t ht a hinj hpos hsum

end Erdos261

open Erdos261 in
theorem solution (n t : ℕ) (ht : 2 ≤ t) (a : Fin t → ℕ) (hinj : a.Injective) (hpos : 1 ≤ a)
    (hsum : (n : ℚ) / 2 ^ n = ∑ k, (a k : ℚ) / 2 ^ (a k)) : ∀ i, n < a i :=
  Erdos261.indices_gt n t ht a hinj hpos hsum

#print axioms solution
