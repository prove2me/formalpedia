-- Prove2me | solution 1 for Erdos287.upper_sieve_type_I_II_levels_below_seven_thirteenths
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T18:05:33.246895+00:00
-- url     : https://prove2.me/submissions/f22e3070-162e-42b3-a225-f0354648a5a8

import Mathlib

set_option autoImplicit false

/-- The upper-only Type I and Type II exponent conditions hold at every
level in the listed interval below 7/13. -/
theorem solution {ι : Type*} [DecidableEq ι] (I smooth : Finset ι) (x : ι → ℝ)
    (hcard : I.card ≤ 8) (hsum : ∑ i ∈ I, x i = 1)
    (hrough : ∀ i ∈ I, i ∉ smooth → x i ≤ 251 / 1000)
    (θ ε : ℝ) (hθlo : 269 / 500 ≤ θ) (_hθhi : θ < 7 / 13)
    (hε : 0 < ε) (hεmax : ε ≤ (7 - 13 * θ) / 1000) :
    let t := (5 * θ + 1) / 12
    ((∃ i ∈ I, i ∈ smooth ∧ t ≤ x i) ∨
      ∃ i ∈ I, 3 / 25 ≤ x i ∧ x i ≤ t) ∧
    (∀ m r s : ℝ, t ≤ m → m ≤ 1 → 0 ≤ r → 0 ≤ s →
      s ≤ m - ε → r ≤ θ - m + 2 * ε →
      (s - m) / 2 ≤ -ε / 2 ∧
      r + s / 2 + 1 / 2 ≤ 1 - ε ∧
      r + s / 4 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      3 * r / 4 + s / 2 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      r / 2 + s / 4 - 3 * m / 4 ≤ -ε) ∧
    (∀ ν r s : ℝ, 3 / 25 ≤ ν → ν ≤ t → 0 ≤ r → 0 ≤ s →
      r + s ≥ 1 / 2 - ε → r ≤ θ - ν + 2 * ε → s ≤ ν - ε →
      r - s / 2 + ν ≤ 1 / 2 - ε ∧
      2 * r + ν ≤ 1 - ε ∧
      r / 2 + 5 * ν / 4 ≤ 1 / 2 - ε ∧
      3 * r / 4 + ν ≤ 1 / 2 - ε ∧
      r + 3 * ν / 2 ≤ 1 - ε) ∧
    269 / (500 : ℝ) ≤ 673 / 1250 ∧ 673 / (1250 : ℝ) < 7 / 13 ∧
    2 / (673 / 1250 : ℝ) < 743 / 200 ∧ 2 / (673 / 1250 : ℝ) < 145 / 39 ∧
    106 / (39 : ℝ) < Real.exp 1 := by
  dsimp
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num, by norm_num, by norm_num,
    by linarith [Real.exp_one_gt_d9]⟩
  · by_cases hlarge : ∃ i ∈ I, i ∈ smooth ∧ (5 * θ + 1) / 12 ≤ x i
    · exact Or.inl hlarge
    right
    by_contra hmiddle
    have hsmall (i : ι) (hi : i ∈ I) : x i ≤ 3 / 25 := by
      have htop : x i ≤ (5 * θ + 1) / 12 := by
        by_cases hs : i ∈ smooth
        · exact le_of_not_ge fun h => hlarge ⟨i, hi, hs, h⟩
        · exact (hrough i hi hs).trans (by linarith)
      exact le_of_not_ge fun h => hmiddle ⟨i, hi, h, htop⟩
    have hall := Finset.sum_le_sum hsmall
    have hcard' : (I.card : ℝ) ≤ 8 := by exact_mod_cast hcard
    simp only [Finset.sum_const, nsmul_eq_mul, hsum] at hall
    linarith
  · intro m r s hm hm' hr hs hs' hr'
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · intro ν r s hν hν' hr hs hsum' hr' hs'
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

