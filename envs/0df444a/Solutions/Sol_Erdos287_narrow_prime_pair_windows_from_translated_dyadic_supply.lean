-- Prove2me | solution 1 for Erdos287.narrow_prime_pair_windows_from_translated_dyadic_supply
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T08:06:49.605796+00:00
-- url     : https://prove2.me/submissions/1f1b98a5-d87c-45ec-8a6e-40d951fe745f

import Mathlib

set_option autoImplicit false

/-- A dyadic prime-pair theorem uniform under linearly bounded translations
also supplies pairs in any prescribed fixed relative window. -/
theorem solution (a : ℕ → ℕ) (N q : ℕ) (hq : 1 ≤ q)
    (hdyadic : ∀ C : ℕ, ∃ H₀ : ℕ, ∀ H : ℕ, H₀ ≤ H → ∀ z : ℕ, z ≤ C * H →
      ∃ n : ℕ, H < n ∧ n ≤ 2 * H ∧ ∃ i j : ℕ, i < j ∧ j < N ∧
        Nat.Prime (a i * (n + z) + 1) ∧ Nat.Prime (a j * (n + z) + 1)) :
    ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T →
      ∃ t : ℕ, T < t ∧ t ≤ T + T / q ∧ ∃ i j : ℕ, i < j ∧ j < N ∧
        Nat.Prime (a i * t + 1) ∧ Nat.Prime (a j * t + 1) := by
  obtain ⟨H₀, hsupply⟩ := hdyadic q
  refine ⟨max H₀ q * q, ?_⟩
  intro T hT
  let H := T / q
  let z := T - H
  have hqpos : 0 < q := hq
  have hH : max H₀ q ≤ H := (Nat.le_div_iff_mul_le hqpos).mpr hT
  have hHT : H ≤ T := Nat.div_le_self _ _
  have hzH : z + H = T := Nat.sub_add_cancel hHT
  have hrem : T % q < q := Nat.mod_lt _ hqpos
  have hsplit : T % q + q * H = T := Nat.mod_add_div _ _
  have hz : z ≤ q * H := by
    have := (le_max_right H₀ q).trans hH
    omega
  obtain ⟨n, hlo, hhi, i, j, hij, hj, hpi, hpj⟩ :=
    hsupply H ((le_max_left _ _).trans hH) z hz
  exact ⟨n + z, by omega, by change n + z ≤ T + H; omega, i, j, hij, hj, hpi, hpj⟩

