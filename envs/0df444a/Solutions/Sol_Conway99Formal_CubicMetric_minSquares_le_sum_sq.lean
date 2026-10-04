-- Prove2me | solution 1 for Conway99Formal.CubicMetric.minSquares_le_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T04:08:00.778974+00:00
-- url     : https://prove2.me/submissions/70c864b3-41e6-4d31-bc7c-e2376b4ddae2

import Definitions.Def_Arithmetic
import Mathlib

namespace Conway99Formal.CubicMetric
end Conway99Formal.CubicMetric

set_option autoImplicit false

namespace Conway99Formal.CubicMetric














































end Conway99Formal.CubicMetric

set_option autoImplicit false

open Conway99Formal.CubicMetric

open Conway99Formal.CubicMetric in
theorem solution {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℤ) (total : ℤ)
    (htotal : ∑ i ∈ s, x i = total) :
    minSquares s.card total ≤ ∑ i ∈ s, (x i) ^ 2 := by
  let m : ℤ := s.card
  let q : ℤ := total / m
  have hpoint (i : ι) :
      (2 * q + 1) * x i - q * (q + 1) ≤ (x i) ^ 2 := by
    by_cases h : x i - q ≤ 0
    · have h' : x i - q - 1 ≤ 0 := by omega
      nlinarith [mul_nonneg_of_nonpos_of_nonpos h h']
    · have h' : 0 ≤ x i - q := by omega
      have h'' : 0 ≤ x i - q - 1 := by omega
      nlinarith [mul_nonneg h' h'']
  have hsum :
      (2 * q + 1) * total - m * q * (q + 1) ≤
        ∑ i ∈ s, (x i) ^ 2 := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ s) => hpoint i)
    have hleft :
        (∑ i ∈ s, ((2 * q + 1) * x i - q * (q + 1))) =
          (2 * q + 1) * total - m * q * (q + 1) := by
      simp [Finset.sum_sub_distrib, ← Finset.mul_sum, htotal, m]
      ring
    rw [hleft] at h
    exact h
  have hdiv : m * (total / m) + total % m = total :=
    Int.mul_ediv_add_emod total m
  have hformula : minSquares m total =
      (2 * q + 1) * total - m * q * (q + 1) := by
    dsimp [minSquares, q]
    linear_combination (2 * (total / m) + 1) * hdiv
  change minSquares m total ≤ ∑ i ∈ s, (x i) ^ 2
  rw [hformula]
  exact hsum
