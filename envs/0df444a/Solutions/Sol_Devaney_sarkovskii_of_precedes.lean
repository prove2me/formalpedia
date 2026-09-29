-- Prove2me | solution 1 for Devaney.sarkovskii_of_precedes
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T13:42:30.192068+00:00
-- url     : https://prove2.me/submissions/8fd7730f-7492-422c-8002-de4ccae9d1a0

import Mathlib
import Definitions.Def_Devaney_sarkovskii
import Theorems.Thm_Devaney_sarkovskii_odd_mul_pow_two
import Theorems.Thm_Devaney_sarkovskii_pow_two

open Devaney

namespace SarkovskiiAux

/-- Every natural number factors as `2 ^ v₂(n) * odd(n)`. -/
theorem twoPow_mul_oddPart (n : ℕ) : 2 ^ twoAdicVal n * oddPart n = n :=
  Nat.mul_div_cancel' pow_padicValNat_dvd

/-- The odd part of a positive number is odd. -/
theorem oddPart_odd (n : ℕ) (hn : 0 < n) : Odd (oddPart n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff]
  by_contra hcon
  obtain ⟨c, hc⟩ : 2 ∣ oddPart n := by omega
  have hfac := twoPow_mul_oddPart n
  rw [hc] at hfac
  have h2 : 2 ^ (padicValNat 2 n + 1) ∣ n := by
    refine ⟨c, ?_⟩
    have e : 2 ^ (padicValNat 2 n + 1) * c = 2 ^ twoAdicVal n * (2 * c) := by
      unfold twoAdicVal; ring
    rw [e]
    exact hfac.symm
  have := (padicValNat_dvd_iff_le (p := 2) (a := n) hn.ne').mp h2
  omega

/-- The odd part of a positive number is positive. -/
theorem oddPart_pos (n : ℕ) (hn : 0 < n) : 0 < oddPart n := by
  rcases Nat.eq_zero_or_pos (oddPart n) with h | h
  · have := twoPow_mul_oddPart n
    rw [h, Nat.mul_zero] at this
    omega
  · exact h

/-- A number with odd part `1` is a power of two. -/
theorem eq_twoPow_of_oddPart_eq_one (n : ℕ) (h : oddPart n = 1) : n = 2 ^ twoAdicVal n := by
  have := twoPow_mul_oddPart n
  rw [h, Nat.mul_one] at this
  omega

end SarkovskiiAux

open SarkovskiiAux

/-- **Sarkovskii's theorem.** -/
theorem solution (f : ℝ → ℝ) (hf : Continuous f) (k l : ℕ)
    (h : ∃ x, HasPrimePeriod f x k) (hkl : SarkovskiiPrecedes k l) :
    ∃ x, HasPrimePeriod f x l := by
  obtain ⟨x, hx⟩ := h
  have hk : 0 < k := hx.1
  by_cases hko : oddPart k = 1
  · -- `k` is a power of two, so the only applicable clause makes `l` a smaller power of two.
    rcases hkl with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, hlo, -, hlt⟩
    · omega
    · omega
    · have hkeq : k = 2 ^ twoAdicVal k := eq_twoPow_of_oddPart_eq_one k hko
      have hleq : l = 2 ^ twoAdicVal l := eq_twoPow_of_oddPart_eq_one l hlo
      rw [hleq]
      refine sarkovskii_pow_two f hf (twoAdicVal k) ⟨x, ?_⟩ (twoAdicVal l) hlt
      rw [← hkeq]
      exact hx
  · -- `k = p * 2 ^ m` with `p > 1` odd.
    obtain ⟨p, m, hp, hp1, rfl⟩ : ∃ p m, Odd p ∧ 1 < p ∧ k = p * 2 ^ m := by
      refine ⟨oddPart k, twoAdicVal k, oddPart_odd k hk, ?_, ?_⟩
      · have := oddPart_pos k hk
        omega
      · rw [mul_comm]
        exact (twoPow_mul_oddPart k).symm
    exact sarkovskii_odd_mul_pow_two f hf p m hp hp1 ⟨x, hx⟩ l hkl
