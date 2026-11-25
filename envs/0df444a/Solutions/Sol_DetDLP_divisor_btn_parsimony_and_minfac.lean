-- Prove2me | solution 1 for DetDLP.divisor_btn_parsimony_and_minfac
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T12:27:37.192959+00:00
-- url     : https://prove2.me/submissions/a766ad8a-7456-4fe4-982e-1e672a06f3d6

import Mathlib
import Definitions.Def_DetDLP_Machine

set_option autoImplicit false

open DetDLP

theorem solution :
    ∀ (N : ℕ), 2 ≤ N →
      let n := bitLen (N + 1)
      N < 2 ^ n ∧
      (∀ d e : ℕ,
        (2 ≤ d ∧ d < N ∧ e < 2 ^ n ∧ d * e = N) ↔
        (2 ≤ d ∧ d < N ∧ d ∣ N ∧ e = N / d)) ∧
      ((Finset.Ico 2 N).filter (fun d => d ∣ N) = ∅ ↔ N.Prime) ∧
      (¬ N.Prime →
        N.minFac ∈ (Finset.Ico 2 N).filter (fun d => d ∣ N) ∧
        N.minFac.Prime ∧
        (∀ d ∈ (Finset.Ico 2 N).filter (fun d => d ∣ N), N.minFac ≤ d) ∧
        2 ≤ N / N.minFac ∧ N / N.minFac < N ∧
        N.primeFactorsList = N.minFac :: (N / N.minFac).primeFactorsList) := by
  intro N hN
  dsimp only
  set n := bitLen (N + 1)
  have hN_lt : N < 2 ^ n := by
    have hpow : N + 1 ≤ 2 ^ n := Nat.le_pow_clog (by decide : 1 < 2) (N + 1)
    omega
  refine ⟨hN_lt, ?_, ?_, ?_⟩
  · intro d e
    constructor
    · rintro ⟨hd2, hdN, _, hde⟩
      have hdvd : d ∣ N := ⟨e, hde.symm⟩
      have he : e = N / d := by
        rw [← hde, Nat.mul_div_right e (by omega)]
      exact ⟨hd2, hdN, hdvd, he⟩
    · rintro ⟨hd2, hdN, hdvd, rfl⟩
      have hde : d * (N / d) = N := Nat.mul_div_cancel' hdvd
      have he_le : N / d ≤ N := Nat.div_le_self N d
      exact ⟨hd2, hdN, lt_of_le_of_lt he_le hN_lt, hde⟩
  · constructor
    · intro hemp
      by_contra hnot
      have hmin_p : N.minFac.Prime := Nat.minFac_prime (by omega : N ≠ 1)
      have hmin_dvd : N.minFac ∣ N := Nat.minFac_dvd N
      have hmin_le : N.minFac ≤ N := Nat.minFac_le (by omega : 0 < N)
      have hmin_lt : N.minFac < N :=
        lt_of_le_of_ne hmin_le (fun heq => hnot (heq ▸ hmin_p))
      have hmem : N.minFac ∈ (Finset.Ico 2 N).filter (fun d => d ∣ N) := by
        rw [Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨hmin_p.two_le, hmin_lt⟩, hmin_dvd⟩
      rw [hemp] at hmem
      exact Finset.notMem_empty _ hmem
    · intro hp
      rw [Finset.filter_eq_empty_iff]
      intro d hd hdvd
      rw [Finset.mem_Ico] at hd
      rcases hp.eq_one_or_self_of_dvd d hdvd with rfl | rfl <;> omega
  · intro hnot
    have hmin_p : N.minFac.Prime := Nat.minFac_prime (by omega : N ≠ 1)
    have hmin_dvd : N.minFac ∣ N := Nat.minFac_dvd N
    have hmin_le : N.minFac ≤ N := Nat.minFac_le (by omega : 0 < N)
    have hmin_lt : N.minFac < N :=
      lt_of_le_of_ne hmin_le (fun heq => hnot (heq ▸ hmin_p))
    have hmem : N.minFac ∈ (Finset.Ico 2 N).filter (fun d => d ∣ N) := by
      rw [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨hmin_p.two_le, hmin_lt⟩, hmin_dvd⟩
    have hle_all : ∀ d ∈ (Finset.Ico 2 N).filter (fun d => d ∣ N), N.minFac ≤ d := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Ico] at hd
      exact Nat.minFac_le_of_dvd (by omega : 2 ≤ d) hd.2
    have hmul_div : N.minFac * (N / N.minFac) = N := Nat.mul_div_cancel' hmin_dvd
    have hdiv_ge2 : 2 ≤ N / N.minFac := by
      by_contra hlt2
      have hle1 : N / N.minFac ≤ 1 := by omega
      have : N ≤ N.minFac * 1 := by
        calc N = N.minFac * (N / N.minFac) := hmul_div.symm
          _ ≤ N.minFac * 1 := Nat.mul_le_mul_left N.minFac hle1
      omega
    have hdiv_lt : N / N.minFac < N := Nat.div_lt_self (by omega : 0 < N) hmin_p.one_lt
    have hpfl : N.primeFactorsList = N.minFac :: (N / N.minFac).primeFactorsList := by
      have hk : N = (N - 2) + 2 := by omega
      conv_lhs => rw [hk, Nat.primeFactorsList_add_two]
      rw [← hk]
    exact ⟨hmem, hmin_p, hle_all, hdiv_ge2, hdiv_lt, hpfl⟩
