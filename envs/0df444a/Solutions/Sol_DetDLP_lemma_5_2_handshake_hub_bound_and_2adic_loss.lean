-- Prove2me | solution 1 for DetDLP.lemma_5_2_handshake_hub_bound_and_2adic_loss
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T14:12:54.256202+00:00
-- url     : https://prove2.me/submissions/793e1f78-f662-4971-9bd3-afe091eb1cd1

import Mathlib

set_option autoImplicit false

private lemma two_pow_modEq_iff (P e : ℕ) (x y : ℤ) :
    ((2 : ℤ) ^ e * x ≡ (2 : ℤ) ^ e * y [ZMOD (2 : ℤ) ^ (P + e)]) ↔
      (x ≡ y [ZMOD (2 : ℤ) ^ P]) := by
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd]
  have hsub : (2 : ℤ) ^ e * y - (2 : ℤ) ^ e * x = (2 : ℤ) ^ e * (y - x) := by ring
  have hpow : (2 : ℤ) ^ (P + e) = (2 : ℤ) ^ e * (2 : ℤ) ^ P := by rw [pow_add, mul_comm]
  rw [hsub, hpow]
  have hne : (2 : ℤ) ^ e ≠ 0 := pow_ne_zero e (by decide)
  exact mul_dvd_mul_iff_left hne

theorem solution :
    (∀ (nV M Δ : ℕ) (deg : Fin nV → ℕ),
      1 ≤ Δ → (∑ v : Fin nV, deg v) ≤ 2 * M →
      Δ * (Finset.univ.filter (fun v : Fin nV => Δ ≤ deg v)).card ≤ 2 * M ∧
      (Finset.univ.filter (fun v : Fin nV => Δ ≤ deg v)).card ≤ 2 * M / Δ) ∧
    (∀ (P e : ℕ) (x y : ℤ),
      ((2 : ℤ) ^ e * x ≡ (2 : ℤ) ^ e * y [ZMOD (2 : ℤ) ^ (P + e)]) ↔
        (x ≡ y [ZMOD (2 : ℤ) ^ P])) ∧
    (∀ (P e c d : ℕ), c < 2 ^ P → d < 2 ^ P →
      ((2 : ℤ) ^ e * (c : ℤ) ≡ (2 : ℤ) ^ e * (d : ℤ) [ZMOD (2 : ℤ) ^ (P + e)]) →
      c = d) := by
  refine ⟨?_, two_pow_modEq_iff, ?_⟩
  · intro nV M Δ deg hΔ hsum
    let H := Finset.univ.filter (fun v : Fin nV => Δ ≤ deg v)
    have hmul : Δ * H.card ≤ 2 * M := by
      calc Δ * H.card
          = ∑ _v ∈ H, Δ := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]; rfl
        _ ≤ ∑ v ∈ H, deg v := by
            refine Finset.sum_le_sum fun v hv => ?_
            exact (Finset.mem_filter.mp hv).2
        _ ≤ ∑ v : Fin nV, deg v :=
            Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
        _ ≤ 2 * M := hsum
    refine ⟨hmul, ?_⟩
    rw [Nat.le_div_iff_mul_le hΔ, mul_comm]
    exact hmul
  · intro P e c d hc hd hmod
    have hmodP := (two_pow_modEq_iff P e (c : ℤ) (d : ℤ)).mp hmod
    have hmodNat : c ≡ d [MOD 2 ^ P] := Int.natCast_modEq_iff.mp hmodP
    rw [Nat.ModEq, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd] at hmodNat
    exact hmodNat
