-- Prove2me | solution 1 for Erdos287.upper_sieve_level_269_over_500_exponents
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T17:59:03.438142+00:00
-- url     : https://prove2.me/submissions/25ad0f74-4d47-44a4-b66a-542c629d9997

import Mathlib

set_option autoImplicit false

/-- A four-fold Heath–Brown decomposition can use single-variable Type II
blocks up to exponent 0.3075 and attain the upper-only sieve target. -/
theorem solution {ι : Type*} [DecidableEq ι] (I smooth : Finset ι) (x : ι → ℝ)
    (hcard : I.card ≤ 8) (hsum : ∑ i ∈ I, x i = 1)
    (hrough : ∀ i ∈ I, i ∉ smooth → x i ≤ 251 / 1000)
    (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ 1 / 100000) :
    let θ : ℝ := 269 / 500
    ((∃ i ∈ I, i ∈ smooth ∧ 123 / 400 ≤ x i) ∨
      ∃ i ∈ I, 3 / 25 ≤ x i ∧ x i ≤ 123 / 400) ∧
    (∀ m r s : ℝ, 123 / 400 ≤ m → m ≤ 1 → 0 ≤ r → 0 ≤ s →
      s ≤ m - ε → r ≤ θ - m + 2 * ε →
      (s - m) / 2 ≤ -ε / 2 ∧
      r + s / 2 + 1 / 2 ≤ 1 - ε ∧
      r + s / 4 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      3 * r / 4 + s / 2 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      r / 2 + s / 4 - 3 * m / 4 ≤ -ε) ∧
    (∀ ν r s : ℝ, 3 / 25 ≤ ν → ν ≤ 123 / 400 → 0 ≤ r → 0 ≤ s →
      r + s ≥ 1 / 2 - ε → r ≤ θ - ν + 2 * ε → s ≤ ν - ε →
      r - s / 2 + ν ≤ 1 / 2 - ε ∧
      2 * r + ν ≤ 1 - ε ∧
      r / 2 + 5 * ν / 4 ≤ 1 / 2 - ε ∧
      3 * r / 4 + ν ≤ 1 / 2 - ε ∧
      r + 3 * ν / 2 ≤ 1 - ε) ∧
    2 / θ < 1 + (1359 / 500 : ℝ) ∧ 1359 / 500 < Real.exp 1 := by
  dsimp
  refine ⟨?_, ?_, ?_, by norm_num, by linarith [Real.exp_one_gt_d9]⟩
  · by_cases hlarge : ∃ i ∈ I, i ∈ smooth ∧ 123 / 400 ≤ x i
    · exact Or.inl hlarge
    right
    by_contra hmiddle
    have hsmall (i : ι) (hi : i ∈ I) : x i ≤ 3 / 25 := by
      have htop : x i ≤ 123 / 400 := by
        by_cases hs : i ∈ smooth
        · exact le_of_not_ge fun h => hlarge ⟨i, hi, hs, h⟩
        · exact (hrough i hi hs).trans (by norm_num)
      exact le_of_not_ge fun h => hmiddle ⟨i, hi, h, htop⟩
    have hall := Finset.sum_le_sum hsmall
    have hcard' : (I.card : ℝ) ≤ 8 := by exact_mod_cast hcard
    simp only [Finset.sum_const, nsmul_eq_mul, hsum] at hall
    linarith
  · intro m r s hm hm' hr hs hs' hr'
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · intro ν r s hν hν' hr hs hsum' hr' hs'
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

