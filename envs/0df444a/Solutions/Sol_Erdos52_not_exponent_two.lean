-- Prove2me | solution 1 for Erdos52.not_exponent_two
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T16:46:07.632163+00:00
-- url     : https://prove2.me/submissions/7fae5184-94f6-40ba-9a50-0ce40fcbd5fe

import Mathlib
open scoped Pointwise

/-!
Erdős's multiplication-table phenomenon (Erdős problem 52): there is no `C > 0` with
`max (|A + A|, |A * A|) ≥ C |A| ^ 2` for all finite `A ⊂ ℤ`.

Construction.  For `t` large put `m = t ^ 4` and let `B_i` (`i < k`) be `k` disjoint blocks of `m`
consecutive primes (indices `i m, …, i m + m - 1` in `Nat.nth Nat.Prime`).  Let
`A = B_0 * B_1 * ⋯ * B_{k-1}` (pointwise products).  By unique factorisation the product map is
injective, so `|A| = m ^ k`.  Since `A * A = ∏ (B_i * B_i)` and `|B_i * B_i| ≤ C(m + 1, 2)`,
`|A * A| ≤ ((5/8) m ^ 2) ^ k = (5/8) ^ k |A| ^ 2`.  Every element of `A` is at most `p ^ k`
where `p` is the `k m`-th prime; Chebyshev's bound `Chebyshev.pi_ge` gives `p ≤ t ^ 6 = m ^ (3/2)`,
so `|A + A| ≤ 2 t ^ (6 k) + 1 < C t ^ (8 k) = C |A| ^ 2`.  Choose `k` with `(5/8) ^ k < C`.
-/

namespace Erdos52.MultTable
open Finset

/-- The `n`-th prime. -/
noncomputable def q (n : ℕ) : ℕ := Nat.nth Nat.Prime n

theorem q_prime (n : ℕ) : (q n).Prime := Nat.prime_nth_prime n

theorem q_strictMono : StrictMono q := Nat.nth_strictMono Nat.infinite_setOfPred_prime

theorem q_injective : Function.Injective q := q_strictMono.injective

/-- The `i`-th block: `m` consecutive primes. -/
noncomputable def blk (m i : ℕ) : Finset ℕ := (range m).image (fun j => q (i * m + j))

/-- The product set of the first `k` blocks. -/
noncomputable def prodSet (m k : ℕ) : Finset ℕ := ∏ i ∈ range k, blk m i

theorem card_blk (m i : ℕ) : (blk m i).card = m := by
  unfold blk
  rw [card_image_of_injective _ ?_, card_range]
  intro a b h
  have := q_injective h
  omega

theorem mem_blk {m i b : ℕ} (hb : b ∈ blk m i) : ∃ j < m, b = q (i * m + j) := by
  unfold blk at hb
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hb
  exact ⟨j, mem_range.mp hj, rfl⟩

theorem prodSet_succ (m k : ℕ) : prodSet m (k + 1) = prodSet m k * blk m k := by
  unfold prodSet
  rw [prod_range_succ]

theorem prodSet_zero (m : ℕ) : prodSet m 0 = {1} := by
  unfold prodSet
  rw [prod_range_zero]
  exact Finset.singleton_one.symm

/-- Every element of the product set is positive and has only prime factors among the first
`k * m` primes. -/
theorem prodSet_prime_factors (m : ℕ) : ∀ k : ℕ, ∀ a ∈ prodSet m k, 0 < a ∧
    ∀ p : ℕ, p.Prime → p ∣ a → ∃ n < k * m, p = q n := by
  intro k
  induction k with
  | zero =>
    intro a ha
    rw [prodSet_zero, mem_singleton] at ha
    subst ha
    refine ⟨by norm_num, fun p hp hpa => ?_⟩
    exact absurd (Nat.le_of_dvd one_pos hpa) (by have := hp.two_le; omega)
  | succ k ih =>
    intro a ha
    rw [prodSet_succ, mem_mul] at ha
    obtain ⟨x, hx, b, hb, rfl⟩ := ha
    obtain ⟨hx0, hxp⟩ := ih x hx
    obtain ⟨j, hj, rfl⟩ := mem_blk hb
    refine ⟨Nat.mul_pos hx0 (q_prime _).pos, fun p hp hpa => ?_⟩
    rcases (Nat.Prime.dvd_mul hp).mp hpa with h | h
    · obtain ⟨n, hn, hpn⟩ := hxp p hp h
      exact ⟨n, by nlinarith, hpn⟩
    · refine ⟨k * m + j, by nlinarith, ?_⟩
      exact (Nat.prime_dvd_prime_iff_eq hp (q_prime _)).mp h

theorem inj_mul (m k : ℕ) :
    ((prodSet m k : Set ℕ) ×ˢ (blk m k : Set ℕ)).InjOn fun p => p.1 * p.2 := by
  intro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
  simp only [Set.mem_prod, mem_coe] at hab hab'
  obtain ⟨ha, hb⟩ := hab
  obtain ⟨ha', hb'⟩ := hab'
  simp only at heq
  obtain ⟨j, hj, rfl⟩ := mem_blk hb
  obtain ⟨j', hj', rfl⟩ := mem_blk hb'
  have hdvd : q (k * m + j) ∣ a' * q (k * m + j') := ⟨a, by rw [← heq]; ring⟩
  have hne : ¬ q (k * m + j) ∣ a' := by
    intro h
    obtain ⟨n, hn, hqn⟩ := (prodSet_prime_factors m k a' ha').2 _ (q_prime _) h
    have := q_injective hqn
    omega
  have hdq : q (k * m + j) ∣ q (k * m + j') := by
    rcases (Nat.Prime.dvd_mul (q_prime _)).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  have hqq := (Nat.prime_dvd_prime_iff_eq (q_prime _) (q_prime _)).mp hdq
  have hpos : 0 < q (k * m + j') := (q_prime _).pos
  rw [hqq] at heq
  have := Nat.eq_of_mul_eq_mul_right hpos heq
  rw [this, hqq]

theorem card_prodSet (m : ℕ) : ∀ k : ℕ, (prodSet m k).card = m ^ k := by
  intro k
  induction k with
  | zero => simp [prodSet_zero]
  | succ k ih =>
    have key : (prodSet m k * blk m k).card = (prodSet m k).card * (blk m k).card := by
      rw [card_mul_iff]
      exact inj_mul m k
    rw [prodSet_succ, key, ih, card_blk, pow_succ]

theorem card_le_prod_card (s : ℕ → Finset ℕ) :
    ∀ k : ℕ, (∏ i ∈ range k, s i).card ≤ ∏ i ∈ range k, (s i).card := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, prod_range_succ]
    exact (card_mul_le).trans (Nat.mul_le_mul ih le_rfl)

theorem card_blk_mul_blk (m i : ℕ) : (blk m i * blk m i).card ≤ (m + 1).choose 2 := by
  classical
  let f : Sym2 ℕ → ℕ := Sym2.lift ⟨fun x y => q (i * m + x) * q (i * m + y),
    fun x y => mul_comm _ _⟩
  have hsub : blk m i * blk m i ⊆ ((range m).sym2).image f := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_mul.mp hz
    obtain ⟨x, hx, rfl⟩ := mem_blk ha
    obtain ⟨y, hy, rfl⟩ := mem_blk hb
    refine mem_image.mpr ⟨s(x, y), ?_, ?_⟩
    · rw [mk_mem_sym2_iff]; exact ⟨mem_range.mpr hx, mem_range.mpr hy⟩
    · simp [f]
  calc (blk m i * blk m i).card ≤ (((range m).sym2).image f).card := card_le_card hsub
    _ ≤ ((range m).sym2).card := card_image_le
    _ = (m + 1).choose 2 := by rw [card_sym2, card_range]

theorem card_prodSet_sq (m k : ℕ) :
    (prodSet m k * prodSet m k).card ≤ ((m + 1).choose 2) ^ k := by
  have h : prodSet m k * prodSet m k = ∏ i ∈ range k, (blk m i * blk m i) := by
    unfold prodSet
    rw [prod_mul_distrib]
  rw [h]
  refine (card_le_prod_card (fun i => blk m i * blk m i) k).trans ?_
  calc ∏ i ∈ range k, (blk m i * blk m i).card ≤ ∏ i ∈ range k, (m + 1).choose 2 :=
        prod_le_prod' (fun i _ => card_blk_mul_blk m i)
    _ = ((m + 1).choose 2) ^ k := by simp

/-- Elements of the product set are bounded by `Q ^ k` if all the primes used are `≤ Q`. -/
theorem prodSet_le (m Q : ℕ) : ∀ k : ℕ, (∀ n < k * m, q n ≤ Q) →
    ∀ a ∈ prodSet m k, a ≤ Q ^ k := by
  intro k
  induction k with
  | zero =>
    intro _ a ha
    rw [prodSet_zero, mem_singleton] at ha
    simp [ha]
  | succ k ih =>
    intro hQ a ha
    rw [prodSet_succ, mem_mul] at ha
    obtain ⟨x, hx, b, hb, rfl⟩ := ha
    obtain ⟨j, hj, rfl⟩ := mem_blk hb
    have hx' := ih (fun n hn => hQ n (by nlinarith)) x hx
    have hb' : q (k * m + j) ≤ Q := hQ _ (by nlinarith)
    rw [pow_succ]
    exact Nat.mul_le_mul hx' hb'

theorem card_add_le (S : Finset ℕ) (M : ℕ) (hS : ∀ a ∈ S, a ≤ M) :
    (S + S).card ≤ 2 * M + 1 := by
  have : S + S ⊆ range (2 * M + 1) := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hz
    have := hS a ha
    have := hS b hb
    rw [mem_range]; omega
  simpa using card_le_card this


/-- Chebyshev: there are more than `k * t ^ 4` primes `≤ t ^ 6` once `t ≥ 12 k + 26`. -/
theorem q_le (k t : ℕ) (ht : 12 * k + 26 ≤ t) : q (k * t ^ 4) ≤ t ^ 6 := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have ht1 : 12 * (k : ℝ) + 26 ≤ (t : ℝ) := by exact_mod_cast ht
  set T : ℝ := (t : ℝ) with hT
  have hT26 : 26 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hlogT : Real.log T ≤ T := (Real.log_le_sub_one_of_pos hT0).trans (by linarith)
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlog2' : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have hcast : (((t ^ 6 : ℕ)) : ℝ) = T ^ 6 := by push_cast; rfl
  have hT6 : 1 < T ^ 6 := one_lt_pow₀ (by linarith) (by norm_num)
  have hlogn : Real.log (((t ^ 6 : ℕ)) : ℝ) = 6 * Real.log T := by
    rw [hcast, Real.log_pow]; norm_num
  have hpos : 0 < Real.log (((t ^ 6 : ℕ)) : ℝ) := by
    rw [hcast]; exact Real.log_pos hT6
  have hlogn1 : Real.log ((((t ^ 6 : ℕ)) : ℝ) + 1) ≤ 1 + 6 * T := by
    rw [hcast]
    have h1 : T ^ 6 + 1 ≤ 2 * T ^ 6 := by linarith
    calc Real.log (T ^ 6 + 1) ≤ Real.log (2 * T ^ 6) :=
          Real.log_le_log (by positivity) h1
      _ = Real.log 2 + 6 * Real.log T := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
      _ ≤ 1 + 6 * T := by linarith
  have hπ := Chebyshev.pi_ge (t ^ 6)
  have hkey : ((k : ℝ) * T ^ 4 + 1) ≤ (((t ^ 6 : ℕ) : ℝ) * Real.log 2 -
      Real.log ((((t ^ 6 : ℕ)) : ℝ) + 1)) / Real.log (((t ^ 6 : ℕ)) : ℝ) := by
    rw [le_div_iff₀ hpos, hlogn, hcast]
    have h5 : 0 < T ^ 5 := by positivity
    have h4 : T ^ 4 ≤ T ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h1 : T ≤ T ^ 5 := by
      calc T = T ^ 1 := (pow_one T).symm
        _ ≤ T ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h6 : T ^ 6 = T * T ^ 5 := by ring
    have hA : ((k : ℝ) * T ^ 4 + 1) * (6 * Real.log T) ≤ ((k : ℝ) * T ^ 4 + 1) * (6 * T) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have hB : ((k : ℝ) * T ^ 4 + 1) * (6 * T) = 6 * k * T ^ 5 + 6 * T := by ring
    have hC : (12 * (k : ℝ) + 26) * T ^ 5 ≤ T * T ^ 5 :=
      mul_le_mul_of_nonneg_right ht1 h5.le
    have hF : T ^ 6 / 2 ≤ T ^ 6 * Real.log 2 := by
      have := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0 : ℝ) ≤ T ^ 6)
      linarith
    have hlogn1' : Real.log (T ^ 6 + 1) ≤ 1 + 6 * T := by rwa [hcast] at hlogn1
    have h5' : 1 ≤ T ^ 5 := by linarith
    nlinarith [mul_nonneg hk0 h5.le]
  have hπ' : ((k * t ^ 4 + 1 : ℕ) : ℝ) ≤ (Nat.primeCounting (t ^ 6) : ℝ) := by
    push_cast
    exact hkey.trans hπ
  have hπn : k * t ^ 4 + 1 ≤ Nat.primeCounting (t ^ 6) := by exact_mod_cast hπ'
  have hcount : k * t ^ 4 < Nat.count Nat.Prime (t ^ 6 + 1) := by
    have : Nat.primeCounting (t ^ 6) = Nat.count Nat.Prime (t ^ 6 + 1) := rfl
    omega
  have := Nat.nth_lt_of_lt_count hcount
  unfold q
  omega


/-- For every `C > 0` there is a finite set of integers with
`max (|A + A|, |A * A|) < C |A| ^ 2`. -/
theorem exists_small (C : ℝ) (hC : 0 < C) :
    ∃ A : Finset ℤ, (max (A + A).card (A * A).card : ℝ) < C * (A.card : ℝ) ^ (2 : ℝ) := by
  obtain ⟨k0, hk0⟩ := exists_pow_lt_of_lt_one hC (by norm_num : (5 / 8 : ℝ) < 1)
  obtain ⟨k, hk, hkC⟩ : ∃ k : ℕ, 1 ≤ k ∧ (5 / 8 : ℝ) ^ k < C :=
    ⟨k0 + 1, by omega, lt_of_le_of_lt
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hk0⟩
  obtain ⟨t, htk, htC⟩ : ∃ t : ℕ, 12 * k + 26 ≤ t ∧ 3 / C ≤ (t : ℝ) := by
    refine ⟨max (12 * k + 26) ⌈3 / C⌉₊, le_max_left _ _, ?_⟩
    exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  have ht2 : 2 ≤ t := by omega
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = t ^ 4 := ⟨_, rfl⟩
  have hm4 : (4 : ℝ) ≤ m := by
    have : 4 ≤ t ^ 4 := by
      calc 4 ≤ 2 ^ 4 := by norm_num
        _ ≤ t ^ 4 := Nat.pow_le_pow_left ht2 4
    rw [hm]; exact_mod_cast this
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = prodSet m k := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Finset ℤ, A = S.image (fun n : ℕ => (n : ℤ)) := ⟨_, rfl⟩
  have hAcard : A.card = t ^ (4 * k) := by
    rw [hA, card_image_of_injective _ Nat.cast_injective, hS, card_prodSet, hm, ← pow_mul]
  refine ⟨A, ?_⟩
  have hAsq : (A.card : ℝ) ^ (2 : ℝ) = ((t : ℝ) ^ (4 * k)) ^ 2 := by
    rw [hAcard, Real.rpow_two, Nat.cast_pow]
  rw [hAsq]
  have hSS : ∀ z ∈ A * A, z ∈ (S * S).image (fun n : ℕ => (n : ℤ)) := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_mul.mp hz
    rw [hA] at hx hy
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
    exact mem_image.mpr ⟨a * b, mem_mul.mpr ⟨a, ha, b, hb, rfl⟩, by push_cast; rfl⟩
  have hAA : (A * A).card ≤ ((m + 1).choose 2) ^ k := by
    have hsub : A * A ⊆ (S * S).image (fun n : ℕ => (n : ℤ)) := hSS
    rw [hS] at hsub
    exact (card_le_card hsub).trans (card_image_le.trans (card_prodSet_sq m k))
  have hchoose : (((m + 1).choose 2 : ℕ) : ℝ) ≤ (5 / 8) * ((m : ℝ) ^ 2) := by
    rw [Nat.cast_choose_two]
    push_cast
    nlinarith
  have hAAr : ((A * A).card : ℝ) < C * ((t : ℝ) ^ (4 * k)) ^ 2 := by
    have h1 : ((A * A).card : ℝ) ≤ (((m + 1).choose 2 : ℕ) : ℝ) ^ k := by exact_mod_cast hAA
    have h2 : (((m + 1).choose 2 : ℕ) : ℝ) ^ k ≤ ((5 / 8) * (m : ℝ) ^ 2) ^ k :=
      pow_le_pow_left₀ (by positivity) hchoose k
    have h3 : ((5 / 8) * (m : ℝ) ^ 2) ^ k = (5 / 8 : ℝ) ^ k * ((t : ℝ) ^ (4 * k)) ^ 2 := by
      rw [mul_pow, hm]; push_cast; ring
    have h4 : 0 < ((t : ℝ) ^ (4 * k)) ^ 2 := by positivity
    calc ((A * A).card : ℝ) ≤ _ := h1.trans h2
      _ = (5 / 8 : ℝ) ^ k * ((t : ℝ) ^ (4 * k)) ^ 2 := h3
      _ < C * ((t : ℝ) ^ (4 * k)) ^ 2 := mul_lt_mul_of_pos_right hkC h4
  have hQ : ∀ n < k * m, q n ≤ t ^ 6 := by
    intro n hn
    have := q_le k t htk
    rw [← hm] at this
    exact (q_strictMono.monotone hn.le).trans this
  have hAAdd : ∀ z ∈ A + A, z ∈ (S + S).image (fun n : ℕ => (n : ℤ)) := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    rw [hA] at hx hy
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
    exact mem_image.mpr ⟨a + b, mem_add.mpr ⟨a, ha, b, hb, rfl⟩, by push_cast; rfl⟩
  have hAdd : (A + A).card ≤ 2 * (t ^ 6) ^ k + 1 := by
    have hsub : A + A ⊆ (S + S).image (fun n : ℕ => (n : ℤ)) := hAAdd
    refine (card_le_card hsub).trans (card_image_le.trans ?_)
    rw [hS] at *
    exact card_add_le _ _ (prodSet_le m (t ^ 6) k hQ)
  have hAddr : ((A + A).card : ℝ) < C * ((t : ℝ) ^ (4 * k)) ^ 2 := by
    have h1 : ((A + A).card : ℝ) ≤ 2 * ((t : ℝ) ^ 6) ^ k + 1 := by exact_mod_cast hAdd
    have hT1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (by omega : 1 ≤ t)
    have hT1' : (1 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 1 < t)
    have hp : (1 : ℝ) < ((t : ℝ) ^ 6) ^ k :=
      one_lt_pow₀ (one_lt_pow₀ hT1' (by norm_num)) (by omega)
    have hq : (t : ℝ) ≤ (t : ℝ) ^ (2 * k) := by
      calc (t : ℝ) = (t : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (t : ℝ) ^ (2 * k) := pow_le_pow_right₀ hT1 (by omega)
    have h3 : 3 ≤ C * (t : ℝ) ^ (2 * k) := by
      have : 3 / C ≤ (t : ℝ) ^ (2 * k) := htC.trans hq
      rw [div_le_iff₀ hC] at this; linarith
    have h5 : ((t : ℝ) ^ (4 * k)) ^ 2 = ((t : ℝ) ^ 6) ^ k * (t : ℝ) ^ (2 * k) := by ring
    have hP : 0 ≤ ((t : ℝ) ^ 6) ^ k := by linarith
    have h6 : ((t : ℝ) ^ 6) ^ k * 3 ≤ ((t : ℝ) ^ 6) ^ k * (C * (t : ℝ) ^ (2 * k)) :=
      mul_le_mul_of_nonneg_left h3 hP
    rw [h5]
    have h7 : C * (((t : ℝ) ^ 6) ^ k * (t : ℝ) ^ (2 * k)) =
        ((t : ℝ) ^ 6) ^ k * (C * (t : ℝ) ^ (2 * k)) := by ring
    linarith
  exact max_lt hAddr hAAr

end Erdos52.MultTable

theorem solution : ¬ ∃ (C : ℝ), 0 < C ∧ ∀ (A : Finset ℤ),
    (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 : ℝ) := by
  rintro ⟨C, hC, h⟩
  obtain ⟨A, hA⟩ := Erdos52.MultTable.exists_small C hC
  exact absurd (h A) (not_le.mpr hA)
