-- Prove2me | solution 1 for Erdos287.sixty_two_billion_unit_gaps_from_explicit_prime_windows
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T07:13:34.141369+00:00
-- url     : https://prove2.me/submissions/742d3415-55d4-4b33-a408-2449470b9a15

import Mathlib
import Theorems.Thm_Erdos287_unit_gaps_from_short_prime_windows

open Finset

set_option autoImplicit false

/-- A prime in each of two short intervals at the top of the denominator
range gives an explicit lower bound on the number of unit gaps. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (hM : 62250000000000 ≤ f (k - 1))
    (hprime : ∀ x d : ℕ, 3 * f (k - 1) ≤ 4 * x → x ≤ f (k - 1) →
      1 ≤ d → d ≤ 2 → ∃ p : ℕ, p.Prime ∧ x ≤ d * p ∧
        (d * p - x) * 250000000000 ≤ x) :
    62000000000 ≤ ((Finset.range (k - 1)).filter (fun i => f (i + 1) - f i = 1)).card := by
  let M := f (k - 1)
  let w := M / 250000000000
  let S := Icc ((3 * M + 3) / 4) (M - (w + 1))
  have hbig : 62250000000000 ≤ M := hM
  have hsize : 249000000000 * (w + 1) ≤ M := by
    have hdiv : w * 250000000000 ≤ M := Nat.div_mul_le_self M _
    have hw : 249 ≤ w := (Nat.le_div_iff_mul_le (by decide)).mpr (by exact hbig)
    omega
  have hwindows (x : ℕ) (hx : x ∈ S) :
      3 * M ≤ 4 * x ∧ x + w < M ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
      x ≤ p ∧ p ≤ x + w ∧ x ≤ 2 * q ∧ 2 * q ≤ x + w := by
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp hx
    have hleft : 3 * M ≤ 4 * x := by omega
    have hright : x + w < M := by omega
    obtain ⟨p, hp, hp₁, hp₂⟩ := hprime x 1 hleft (by omega) (by decide) (by decide)
    obtain ⟨q, hq, hq₁, hq₂⟩ := hprime x 2 hleft (by omega) (by decide) (by decide)
    have hq₃ : 2 * q - x ≤ w :=
      (Nat.le_div_iff_mul_le (by decide)).mpr (hq₂.trans (by omega))
    have hp₃ : 1 * p - x ≤ w :=
      (Nat.le_div_iff_mul_le (by decide)).mpr (hp₂.trans (by omega))
    exact ⟨hleft, hright, p, q, hp, hq, by omega, by omega, hq₁, by omega⟩
  have hcount := Erdos287.unit_gaps_from_short_prime_windows k hk f hf1 hmono hsum hgap
    (show 12 ≤ M by omega) S w hwindows
  have hS : M ≤ 4 * S.card + 4 * (w + 1) := by
    simp only [S, Nat.card_Icc]
    omega
  by_contra! ht
  have ht' : (w + 1) * ((Finset.range (k - 1)).filter
      (fun i => f (i + 1) - f i = 1)).card ≤ (w + 1) * 61999999999 :=
    Nat.mul_le_mul_left _ (by omega)
  have hupper : S.card ≤ (w + 1) * 61999999999 := hcount.trans ht'
  omega

