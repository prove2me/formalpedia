-- Prove2me | solution 1 for DetDLP.factor_splitting_tree_correctness
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T13:33:31.566792+00:00
-- url     : https://prove2.me/submissions/f3cde21c-89d1-4a1f-a622-efd4f3880775

import Mathlib
import Definitions.Def_DetDLP_Machine

set_option autoImplicit false

open DetDLP

private def splitRec (f : ℕ → ℕ) : ℕ → ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun x => [x]) (fun _ prev x =>
    let d := f x
    if 2 ≤ d ∧ d < x ∧ d ∣ x then prev d ++ prev (x / d) else [x])

private lemma proper_div_quot_bounds {x d : ℕ} (hd2 : 2 ≤ d) (hdx : d < x) (hdvd : d ∣ x) :
    2 ≤ x / d ∧ d * 2 ≤ x ∧ (x / d) * 2 ≤ x := by
  have hmul : d * (x / d) = x := Nat.mul_div_cancel' hdvd
  have hq2 : 2 ≤ x / d := by
    generalize x / d = q at hmul ⊢
    by_contra hlt
    have h01 : q = 0 ∨ q = 1 := by omega
    rcases h01 with h0 | h1 <;> nlinarith
  refine ⟨hq2, ?_, ?_⟩
  · calc d * 2 ≤ d * (x / d) := Nat.mul_le_mul_left d hq2
      _ = x := hmul
  · calc (x / d) * 2 ≤ (x / d) * d := Nat.mul_le_mul_left (x / d) hd2
      _ = x := by rw [mul_comm, hmul]

private lemma splitRec_prod (f : ℕ → ℕ) :
    ∀ (k x : ℕ), 2 ≤ x → (splitRec f k x).prod = x
  | 0, x, _ => by
    change [x].prod = x
    simp
  | k + 1, x, hx => by
    change (if 2 ≤ f x ∧ f x < x ∧ f x ∣ x then
      splitRec f k (f x) ++ splitRec f k (x / f x) else [x]).prod = x
    split_ifs with h
    · rcases h with ⟨hd2, hdx, hdvd⟩
      obtain ⟨hq2, _, _⟩ := proper_div_quot_bounds hd2 hdx hdvd
      rw [List.prod_append, splitRec_prod f k (f x) hd2, splitRec_prod f k (x / f x) hq2,
        Nat.mul_div_cancel' hdvd]
    · simp

private lemma splitRec_all_prime (f : ℕ → ℕ)
    (hf : ∀ N : ℕ, 2 ≤ N → ¬ N.Prime → 2 ≤ f N ∧ f N < N ∧ f N ∣ N) :
    ∀ (k x : ℕ), 2 ≤ x → x < 2 ^ (k + 1) → ∀ p ∈ splitRec f k x, p.Prime
  | 0, x, hx, hlt => by
    exfalso
    omega
  | k + 1, x, hx, hlt => by
    change ∀ p ∈ (if 2 ≤ f x ∧ f x < x ∧ f x ∣ x then
      splitRec f k (f x) ++ splitRec f k (x / f x) else [x]), p.Prime
    by_cases hprime : x.Prime
    · have hnot : ¬ (2 ≤ f x ∧ f x < x ∧ f x ∣ x) := by
        rintro ⟨hd2, hdx, hdvd⟩
        rcases hprime.eq_one_or_self_of_dvd (f x) hdvd with h1 | hself <;> omega
      rw [if_neg hnot]
      intro p hp
      simp only [List.mem_singleton] at hp
      rwa [hp]
    · have h := hf x hx hprime
      rw [if_pos h]
      rcases h with ⟨hd2, hdx, hdvd⟩
      obtain ⟨hq2, hd_half, hq_half⟩ := proper_div_quot_bounds hd2 hdx hdvd
      have hpow : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) * 2 := by ring
      have hd_lt : f x < 2 ^ (k + 1) := by omega
      have hq_lt : x / f x < 2 ^ (k + 1) := by omega
      intro p hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · exact splitRec_all_prime f hf k (f x) hd2 hd_lt p hp
      · exact splitRec_all_prime f hf k (x / f x) hq2 hq_lt p hp

theorem solution :
    ∀ (f : ℕ → ℕ),
      (∀ N : ℕ, 2 ≤ N → ¬ N.Prime → 2 ≤ f N ∧ f N < N ∧ f N ∣ N) →
      let split : ℕ → ℕ → List ℕ :=
        Nat.rec (motive := fun _ => ℕ → List ℕ) (fun x => [x]) (fun _ prev x =>
          let d := f x
          if 2 ≤ d ∧ d < x ∧ d ∣ x then prev d ++ prev (x / d) else [x])
      ∀ N : ℕ, 2 ≤ N →
        let n := bitLen (N + 1)
        (split n N).prod = N ∧
        (∀ p ∈ split n N, p.Prime) ∧
        ((split n N).mergeSort) = N.primeFactorsList := by
  intro f hf
  dsimp only
  intro N hN
  change (splitRec f (bitLen (N + 1)) N).prod = N ∧
    (∀ p ∈ splitRec f (bitLen (N + 1)) N, p.Prime) ∧
    (splitRec f (bitLen (N + 1)) N).mergeSort = N.primeFactorsList
  have hprod : (splitRec f (bitLen (N + 1)) N).prod = N :=
    splitRec_prod f (bitLen (N + 1)) N hN
  have hN_lt : N < 2 ^ (bitLen (N + 1) + 1) := by
    unfold bitLen
    have h1 : N + 1 ≤ 2 ^ Nat.clog 2 (N + 1) := Nat.le_pow_clog (by decide) (N + 1)
    have h2 : 2 ^ Nat.clog 2 (N + 1) ≤ 2 ^ (Nat.clog 2 (N + 1) + 1) :=
      Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
    omega
  have hprime : ∀ p ∈ splitRec f (bitLen (N + 1)) N, p.Prime :=
    splitRec_all_prime f hf (bitLen (N + 1)) N hN hN_lt
  refine ⟨hprod, hprime, ?_⟩
  have hperm_ms : ((splitRec f (bitLen (N + 1)) N).mergeSort).Perm
      (splitRec f (bitLen (N + 1)) N) :=
    List.mergeSort_perm (splitRec f (bitLen (N + 1)) N) _
  have hprod_ms : ((splitRec f (bitLen (N + 1)) N).mergeSort).prod = N := by
    rw [hperm_ms.prod_eq, hprod]
  have hprime_ms : ∀ p ∈ (splitRec f (bitLen (N + 1)) N).mergeSort, p.Prime :=
    fun p hp => hprime p (hperm_ms.subset hp)
  have hperm_pf : ((splitRec f (bitLen (N + 1)) N).mergeSort).Perm N.primeFactorsList :=
    Nat.primeFactorsList_unique hprod_ms hprime_ms
  have hsorted_ms : ((splitRec f (bitLen (N + 1)) N).mergeSort).Pairwise (· ≤ ·) := by
    have hpw := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact le_trans hab hbc)
      (fun a b => by
        rcases le_total a b with h | h <;> simp [h])
      (splitRec f (bitLen (N + 1)) N)
    exact hpw.imp (by intro a b h; exact of_decide_eq_true h)
  have hsorted_pf : N.primeFactorsList.Pairwise (· ≤ ·) :=
    (Nat.primeFactorsList_sorted N).pairwise
  exact hperm_pf.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2) hsorted_ms hsorted_pf
