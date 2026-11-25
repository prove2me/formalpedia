-- Prove2me | solution 1 for DetDLP.section5_guard_and_kronecker
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T11:23:57.010224+00:00
-- url     : https://prove2.me/submissions/a2fac1c4-7dc5-4900-b023-e4d3d55b84b3

import Mathlib

set_option autoImplicit false

private lemma natPoly_coeff_le_eval_one (q : Polynomial ℕ) (d : ℕ) :
    q.coeff d ≤ q.eval 1 := by
  by_cases hd : d ≤ q.natDegree
  · rw [Polynomial.eval_eq_sum_range]
    have hmem : d ∈ Finset.range (q.natDegree + 1) := Finset.mem_range.mpr (by omega)
    have hle := Finset.single_le_sum (fun i _ => Nat.zero_le (q.coeff i * 1 ^ i)) hmem
    simpa using hle
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact Nat.zero_le _

theorem solution :
    (∀ P0 Qguard r acc : ℕ,
      r < 2 ^ P0 →
      acc < 2 ^ (P0 + Qguard) →
      (acc : ℤ) ≡ ((2 ^ Qguard * r : ℕ) : ℤ) [ZMOD ((2 ^ (P0 + Qguard) : ℕ) : ℤ)] →
      acc = 2 ^ Qguard * r ∧ acc / 2 ^ Qguard = r) ∧
    (∀ K0 ℓ : ℕ, 1 ≤ K0 → 1 ≤ ℓ →
      (∀ i1 i1' i2 i2' : ℕ, i1 < K0 → i1' < K0 →
        i1 + K0 * i2 = i1' + K0 * i2' → i1 = i1' ∧ i2 = i2') ∧
      (∀ i1 i2 : ℕ, i1 < K0 → i2 < ℓ → i1 + K0 * i2 < K0 * ℓ) ∧
      (∀ i1 i2 : ℕ, ℓ ≤ i2 → K0 * ℓ ≤ i1 + K0 * i2)) ∧
    (∀ (n B : ℕ) (p : Fin n → Polynomial ℕ),
      (∀ j : Fin n, (p j).eval 1 ≤ B) →
      (∏ j : Fin n, p j).eval 1 ≤ B ^ n ∧
      ∀ d : ℕ, (∏ j : Fin n, p j).coeff d ≤ B ^ n) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: 2-adic guard-bit exact recovery
    intro P0 Qguard r acc hr hacc hmod
    have hr_bound : 2 ^ Qguard * r < 2 ^ (P0 + Qguard) := by
      rw [Nat.pow_add, mul_comm (2 ^ P0)]
      exact Nat.mul_lt_mul_of_pos_left hr (by positivity)
    have hmodN : acc ≡ 2 ^ Qguard * r [MOD 2 ^ (P0 + Qguard)] :=
      Int.natCast_modEq_iff.mp hmod
    have heq : acc = 2 ^ Qguard * r := by
      change acc % 2 ^ (P0 + Qguard) = (2 ^ Qguard * r) % 2 ^ (P0 + Qguard) at hmodN
      rw [Nat.mod_eq_of_lt hacc, Nat.mod_eq_of_lt hr_bound] at hmodN
      exact hmodN
    refine ⟨heq, ?_⟩
    rw [heq, mul_comm]
    exact Nat.mul_div_left r (by positivity)
  · -- Part 2: Kronecker packing injectivity and truncation bounds
    intro K0 ℓ hK0 hℓ
    refine ⟨?_, ?_, ?_⟩
    · intro i1 i1' i2 i2' h1 h1' heq
      have hmod := congrArg (· % K0) heq
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h1'] at hmod
      have hmul : K0 * i2 = K0 * i2' := by
        rw [hmod] at heq
        exact Nat.add_left_cancel heq
      exact ⟨hmod, Nat.eq_of_mul_eq_mul_left hK0 hmul⟩
    · intro i1 i2 hi1 hi2
      have h2 : i2 + 1 ≤ ℓ := hi2
      calc i1 + K0 * i2 < K0 + K0 * i2 := Nat.add_lt_add_right hi1 (K0 * i2)
        _ = K0 * (i2 + 1) := by ring
        _ ≤ K0 * ℓ := Nat.mul_le_mul_left K0 h2
    · intro i1 i2 hle
      calc K0 * ℓ ≤ K0 * i2 := Nat.mul_le_mul_left K0 hle
        _ ≤ i1 + K0 * i2 := Nat.le_add_left _ _
  · -- Part 3: Nonnegative polynomial L1-norm submultiplicativity
    intro n B p hp
    have heval : (∏ j : Fin n, p j).eval 1 ≤ B ^ n := by
      rw [Polynomial.eval_prod]
      calc ∏ j : Fin n, (p j).eval 1
          ≤ ∏ _j : Fin n, B := Finset.prod_le_prod' fun j _ => hp j
        _ = B ^ n := by simp
    refine ⟨heval, fun d => le_trans (natPoly_coeff_le_eval_one _ d) heval⟩
