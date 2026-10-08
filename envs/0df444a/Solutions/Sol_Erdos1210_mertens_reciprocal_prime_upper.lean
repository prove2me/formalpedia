-- Prove2me | solution 1 for Erdos1210.mertens_reciprocal_prime_upper
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T20:56:08.936903+00:00
-- url     : https://prove2.me/submissions/b0a8024b-fedd-4d02-b52a-820cf7cc6a20

import Mathlib

open Finset Real

lemma pow_div_dvd_factorial (p N : ℕ) (hp : p.Prime) : p ^ (N / p) ∣ N.factorial := by
  rw [hp.pow_dvd_factorial_iff (b := N + 1) (Nat.lt_succ_of_le (Nat.log_le_self _ _))]
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · have hmem : 1 ∈ Ico 1 (N + 1) := by simp; omega
    have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun _ _ => Nat.zero_le _) hmem
    simpa using this

lemma prod_pow_div_dvd_factorial (N : ℕ) :
    ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → ∏ p ∈ s, p ^ (N / p) ∣ N.factorial := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro hs
    rw [Finset.prod_insert ha]
    have hpa : a.Prime := hs a (Finset.mem_insert_self a s)
    have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · apply Nat.Coprime.prod_right
      intro p hp
      apply Nat.Coprime.pow
      exact (Nat.coprime_primes hpa (hs' p hp)).mpr (fun h => ha (h ▸ hp))
    · exact pow_div_dvd_factorial a N hpa
    · exact ih hs'

lemma mertens_first (N : ℕ) :
    ∑ p ∈ filter Nat.Prime (range (N + 1)), Real.log p / p ≤ Real.log N + Real.log 4 := by
  set P := filter Nat.Prime (range (N + 1)) with hP
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (mem_filter.1 hp).2
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    have : P = ∅ := by rw [hP]; decide
    rw [this]; simp only [sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  -- upper bound from the factorial
  have hle : ∏ p ∈ P, p ^ (N / p) ≤ N ^ N :=
    (Nat.le_of_dvd (Nat.factorial_pos N) (prod_pow_div_dvd_factorial N P hPp)).trans
      (Nat.factorial_le_pow N)
  have hle' : ∑ p ∈ P, ((N / p : ℕ) : ℝ) * Real.log p ≤ N * Real.log N := by
    have h1 : ((∏ p ∈ P, p ^ (N / p) : ℕ) : ℝ) ≤ ((N ^ N : ℕ) : ℝ) := by exact_mod_cast hle
    have hpos : (0 : ℝ) < ((∏ p ∈ P, p ^ (N / p) : ℕ) : ℝ) := by
      have : 0 < ∏ p ∈ P, p ^ (N / p) :=
        Finset.prod_pos fun p hp => pow_pos (hPp p hp).pos _
      exact_mod_cast this
    have h2 := Real.log_le_log hpos h1
    rw [Nat.cast_prod, Real.log_prod (fun p hp => by
      have := (hPp p hp).pos
      positivity)] at h2
    simpa [Real.log_pow] using h2
  -- theta bound
  have htheta : ∑ p ∈ P, Real.log p ≤ N * Real.log 4 := by
    have h1 : ((primorial N : ℕ) : ℝ) ≤ ((4 ^ N : ℕ) : ℝ) := by
      exact_mod_cast primorial_le_4_pow N
    have hpos : (0 : ℝ) < ((primorial N : ℕ) : ℝ) := by exact_mod_cast primorial_pos N
    have h2 := Real.log_le_log hpos h1
    unfold primorial at h2
    rw [Nat.cast_prod, Real.log_prod (fun p hp => by
      have := (hPp p hp).pos
      positivity)] at h2
    simpa [Real.log_pow] using h2
  have hfl : ∀ p ∈ P, ((N : ℝ) / p - 1) * Real.log p ≤ ((N / p : ℕ) : ℝ) * Real.log p := by
    intro p hp
    have hp1 := (hPp p hp).one_lt
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp1.le)
    apply mul_le_mul_of_nonneg_right _ hlog
    rw [← Nat.floor_div_eq_div (K := ℝ)]
    exact (Nat.sub_one_lt_floor _).le
  have hsum := Finset.sum_le_sum hfl
  have heq : ∑ p ∈ P, ((N : ℝ) / p - 1) * Real.log p
      = N * ∑ p ∈ P, Real.log p / p - ∑ p ∈ P, Real.log p := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun p _ => ?_
    ring
  have hmain : (N : ℝ) * ∑ p ∈ P, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    linarith
  exact le_of_mul_le_mul_left hmain hNr

lemma step_ineq (S B L0 L1 : ℝ) (hS : S ≤ L0 + B) (h0 : 0 < L0) (h01 : L0 ≤ L1) :
    S / L0 - S / L1 - B / L0 + B / L1 ≤ Real.log L1 - Real.log L0 := by
  have h1 : 0 < L1 := lt_of_lt_of_le h0 h01
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos h1 h0)
  rw [Real.log_div h1.ne' h0.ne', inv_div] at hl
  have e1 : S / L0 - S / L1 - B / L0 + B / L1 = (S - B) * (L1 - L0) / (L0 * L1) := by
    field_simp; ring
  have e2 : (S - B) * (L1 - L0) / (L0 * L1) ≤ L0 * (L1 - L0) / (L0 * L1) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (by linarith)) (by positivity)
  have e3 : L0 * (L1 - L0) / (L0 * L1) = 1 - L0 / L1 := by
    field_simp
  linarith

theorem solution :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      Finset.sum (Finset.filter Nat.Prime (Finset.range n)) (fun p => 1 / (p : ℝ)) ≤
        Real.log (Real.log (n : ℝ)) + C := by
  set B : ℝ := Real.log 4 with hB
  let T : ℕ → ℝ := fun N => ∑ x ∈ range (N + 1), if x.Prime then 1 / (x : ℝ) else 0
  let S : ℕ → ℝ := fun N => ∑ x ∈ range (N + 1), if x.Prime then Real.log x / (x : ℝ) else 0
  have hS : ∀ N, S N ≤ Real.log N + B := by
    intro N
    have := mertens_first N
    simp only [S, ← Finset.sum_filter]
    exact this
  set c0 : ℝ := T 2 - S 2 / Real.log 2 - Real.log (Real.log 2) + B / Real.log 2 with hc0
  have hind : ∀ N, 2 ≤ N →
      T N - S N / Real.log N - Real.log (Real.log N) + B / Real.log N ≤ c0 := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp [hc0]
    | succ N hN ih =>
      have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
      have hL0 : 0 < Real.log N := Real.log_pos (by linarith)
      have hL01 : Real.log N ≤ Real.log (N + 1) := Real.log_le_log (by linarith) (by linarith)
      have hL1 : 0 < Real.log (N + 1) := lt_of_lt_of_le hL0 hL01
      have hT : T (N + 1) = T N + if (N + 1).Prime then 1 / ((N : ℝ) + 1) else 0 := by
        simp only [T]; rw [Finset.sum_range_succ (n := N + 1)]; push_cast; rfl
      have hS' : S (N + 1) = S N +
          if (N + 1).Prime then Real.log ((N : ℝ) + 1) / ((N : ℝ) + 1) else 0 := by
        simp only [S]; rw [Finset.sum_range_succ (n := N + 1)]; push_cast; rfl
      have hred : T (N + 1) - S (N + 1) / Real.log (N + 1 : ℕ) =
          T N - S N / Real.log (N + 1) := by
        rw [hT, hS']
        push_cast
        split_ifs
        · field_simp; ring
        · simp
      have key := step_ineq (S N) B (Real.log N) (Real.log (N + 1)) (hS N) hL0 hL01
      have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hred ⊢
      linarith
  refine ⟨2 + |c0|, ?_⟩
  intro n hn
  rcases Nat.lt_or_ge n 3 with h | h
  · have hn2 : n = 2 := by omega
    subst hn2
    have hE : filter Nat.Prime (range 2) = ∅ := by decide
    rw [hE, Finset.sum_empty]
    have hl2 : (1 : ℝ) / 2 < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hl2' : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have : Real.log (1 / 2) ≤ Real.log (Real.log 2) := Real.log_le_log (by norm_num) hl2.le
    rw [one_div, Real.log_inv] at this
    have := abs_nonneg c0
    push_cast
    linarith
  · obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    have hN : 2 ≤ N := by omega
    have h1 := hind N hN
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hL0 : 0 < Real.log N := Real.log_pos (by linarith)
    have hTeq : Finset.sum (Finset.filter Nat.Prime (Finset.range (N + 1)))
        (fun p => 1 / (p : ℝ)) = T N := by
      simp only [T, Finset.sum_filter]
    rw [hTeq]
    have hSd : S N / Real.log N ≤ 1 + B / Real.log N := by
      rw [div_le_iff₀ hL0, add_mul, div_mul_cancel₀ _ hL0.ne']
      linarith [hS N]
    have hll : Real.log (Real.log N) ≤ Real.log (Real.log ((N + 1 : ℕ) : ℝ)) := by
      apply Real.log_le_log hL0
      apply Real.log_le_log (by linarith)
      push_cast; linarith
    have := le_abs_self c0
    linarith
