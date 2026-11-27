-- Prove2me | solution 1 for Erdos287.asymmetric_chen_type_one_and_two_exponent_margins
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-27T00:58:45.303716+00:00
-- url     : https://prove2.me/submissions/92016557-f4d6-43c5-aa0f-4c4270879ad5

import Mathlib

set_option autoImplicit false

/-- Both asymmetric Chen levels fit a single pair of Type I and Type II
exponent ranges. The same ranges cover every normalized Heath–Brown box. -/
theorem solution {ι : Type*} [DecidableEq ι] (I smooth : Finset ι) (x : ι → ℝ)
    (hcard : I.card ≤ 8) (hsum : ∑ i ∈ I, x i = 1)
    (hrough : ∀ i ∈ I, i ∉ smooth → x i ≤ 251 / 1000)
    (θ ε : ℝ) (hθ : θ ≤ 2127 / 4000) (hε : 0 < ε) (hεmax : ε ≤ 1 / 10000) :
    ((∃ i ∈ I, i ∈ smooth ∧ 3 / 10 ≤ x i) ∨
      ∃ i ∈ I, 3 / 25 ≤ x i ∧ x i ≤ 3 / 10) ∧
    (∀ m r s : ℝ, 3 / 10 ≤ m → m ≤ 1 → 0 ≤ r → 0 ≤ s →
      s ≤ m - ε → r ≤ θ - m + 2 * ε →
      (s - m) / 2 ≤ -ε / 2 ∧
      r + s / 2 + 1 / 2 ≤ 1 - ε ∧
      r + s / 4 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      3 * r / 4 + s / 2 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      r / 2 + s / 4 - 3 * m / 4 ≤ -ε) ∧
    (∀ ν r s : ℝ, 3 / 25 ≤ ν → ν ≤ 3 / 10 → 0 ≤ r → 0 ≤ s →
      r + s ≥ 1 / 2 - ε → r ≤ θ - ν + 2 * ε → s ≤ ν - ε →
      r - s / 2 + ν ≤ 1 / 2 - ε ∧
      2 * r + ν ≤ 1 - ε ∧
      r / 2 + 5 * ν / 4 ≤ 1 / 2 - ε ∧
      3 * r / 4 + ν ≤ 1 / 2 - ε ∧
      r + 3 * ν / 2 ≤ 1 - ε) := by
  refine ⟨?_, ?_, ?_⟩
  · by_cases hlarge : ∃ i ∈ I, i ∈ smooth ∧ 3 / 10 ≤ x i
    · exact Or.inl hlarge
    right
    by_contra hmid
    have hsmall (i : ι) (hi : i ∈ I) : x i ≤ 3 / 25 := by
      have htop : x i ≤ 3 / 10 := by
        by_cases hs : i ∈ smooth
        · exact le_of_not_ge fun h => hlarge ⟨i, hi, hs, h⟩
        · exact (hrough i hi hs).trans (by norm_num)
      exact le_of_not_ge fun h => hmid ⟨i, hi, h, htop⟩
    have hall := Finset.sum_le_sum hsmall
    have hcard' : (I.card : ℝ) ≤ 8 := by exact_mod_cast hcard
    simp only [Finset.sum_const, nsmul_eq_mul, hsum] at hall
    linarith
  · intro m r s hm hm' hr hs hs' hr'
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · intro ν r s hν hν' hr hs hsum' hr' hs'
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

