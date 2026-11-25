-- Prove2me | solution 1 for DetDLP.splitting_tree_size_and_prime_power_from_factors
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T14:03:19.265047+00:00
-- url     : https://prove2.me/submissions/96ea35a1-4526-4d02-b1a1-2f248111f722

import Mathlib
import Definitions.Def_DetDLP_Machine

set_option autoImplicit false

open DetDLP

private def splitRec (f : ℕ → ℕ) : ℕ → ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun x => [x]) (fun _ prev x =>
    let d := f x
    if 2 ≤ d ∧ d < x ∧ d ∣ x then prev d ++ prev (x / d) else [x])

private lemma proper_div_quot_ge_two {x d : ℕ} (hd2 : 2 ≤ d) (hdx : d < x) (hdvd : d ∣ x) :
    2 ≤ x / d := by
  have hmul : d * (x / d) = x := Nat.mul_div_cancel' hdvd
  generalize x / d = q at hmul ⊢
  by_contra hlt
  have h01 : q = 0 ∨ q = 1 := by omega
  rcases h01 with h0 | h1 <;> nlinarith

private lemma splitRec_len_pow_le (f : ℕ → ℕ) :
    ∀ (k x : ℕ), 2 ≤ x → 1 ≤ (splitRec f k x).length ∧ 2 ^ (splitRec f k x).length ≤ x
  | 0, x, hx => by
    change 1 ≤ [x].length ∧ 2 ^ [x].length ≤ x
    simp [hx]
  | k + 1, x, hx => by
    change 1 ≤ (if 2 ≤ f x ∧ f x < x ∧ f x ∣ x then
        splitRec f k (f x) ++ splitRec f k (x / f x) else [x]).length ∧
      2 ^ (if 2 ≤ f x ∧ f x < x ∧ f x ∣ x then
        splitRec f k (f x) ++ splitRec f k (x / f x) else [x]).length ≤ x
    split_ifs with h
    · rcases h with ⟨hd2, hdx, hdvd⟩
      have hq2 := proper_div_quot_ge_two hd2 hdx hdvd
      obtain ⟨hlen1, hpow1⟩ := splitRec_len_pow_le f k (f x) hd2
      obtain ⟨hlen2, hpow2⟩ := splitRec_len_pow_le f k (x / f x) hq2
      rw [List.length_append, pow_add]
      refine ⟨by omega, ?_⟩
      calc 2 ^ (splitRec f k (f x)).length * 2 ^ (splitRec f k (x / f x)).length
          ≤ f x * (x / f x) := Nat.mul_le_mul hpow1 hpow2
        _ = x := Nat.mul_div_cancel' hdvd
    · simp [hx]

theorem solution :
    (∀ (f : ℕ → ℕ),
      let split : ℕ → ℕ → List ℕ :=
        Nat.rec (motive := fun _ => ℕ → List ℕ) (fun x => [x]) (fun _ prev x =>
          let d := f x
          if 2 ≤ d ∧ d < x ∧ d ∣ x then prev d ++ prev (x / d) else [x])
      (∀ (k x : ℕ), 2 ≤ x → 1 ≤ (split k x).length ∧ 2 ^ (split k x).length ≤ x) ∧
      (∀ (N : ℕ), 2 ≤ N →
        let n := bitLen (N + 1)
        (split n N).length ≤ n)) ∧
    (∀ (n : ℕ), 1 ≤ n →
      (∀ r : ℕ, r ∈ n.primeFactors ↔ r ∈ n.primeFactorsList) ∧
      n.primeFactorsList.prod = n ∧
      n.primeFactors.card ≤ n.primeFactorsList.length) := by
  constructor
  · intro f
    dsimp only
    refine ⟨splitRec_len_pow_le f, fun N hN => ?_⟩
    have hpow : 2 ^ (splitRec f (bitLen (N + 1)) N).length ≤ N :=
      (splitRec_len_pow_le f (bitLen (N + 1)) N hN).2
    have hN_lt : N < 2 ^ bitLen (N + 1) := by
      unfold bitLen
      have h1 : N + 1 ≤ 2 ^ Nat.clog 2 (N + 1) := Nat.le_pow_clog (by decide) (N + 1)
      omega
    have hpow_lt : 2 ^ (splitRec f (bitLen (N + 1)) N).length < 2 ^ bitLen (N + 1) :=
      lt_of_le_of_lt hpow hN_lt
    exact le_of_lt ((Nat.pow_lt_pow_iff_right (by decide)).mp hpow_lt)
  · intro n hn
    have hne : n ≠ 0 := by omega
    have hmem : ∀ r : ℕ, r ∈ n.primeFactors ↔ r ∈ n.primeFactorsList := by
      intro r
      rw [Nat.mem_primeFactors, Nat.mem_primeFactorsList hne]
      simp [hne]
    have htoFinset : n.primeFactors = n.primeFactorsList.toFinset := by
      ext r
      rw [List.mem_toFinset, hmem]
    refine ⟨hmem, Nat.prod_primeFactorsList hne, ?_⟩
    rw [htoFinset]
    exact List.toFinset_card_le n.primeFactorsList
