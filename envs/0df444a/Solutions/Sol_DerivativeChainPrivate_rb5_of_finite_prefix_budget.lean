-- Prove2me | solution 1 for DerivativeChainPrivate.rb5_of_finite_prefix_budget
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-18T01:55:50.392869+00:00
-- url     : https://prove2.me/submissions/a8a4a94d-45de-4d1f-8a6e-16fbdd9a09e9

import Theorems.Thm_DerivativeChainPrivate_rb5_scalar
import Mathlib.Analysis.Complex.Norm

set_option autoImplicit false
open scoped BigOperators

theorem solution {ι : Type*} [Fintype ι]
    (w T : ι → ℝ) (Z : ι → ℂ) (a S L N c u V : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hpath : ∀ i, L ≤ T i + ‖(a : ℂ) - Z i‖ + S)
    (hsuffix : S ≤ 1 - |a|)
    (hprefix : (∑ i, w i * T i) ≤ c * Real.sqrt (V / N))
    (hendpoint : (∑ i, w i * ‖Z i‖) ≤ Real.sqrt (u ^ 2 + c * V / N))
    (hc : 0 ≤ c) (hNc : c < N) (hV : 0 ≤ V) (huV : u ^ 2 + V ≤ 1) :
    L ≤ 1 + Real.sqrt (1 + c ^ 2 / (N - c)) := by
  have hpoint (i : ι) : L ≤ 1 + ‖Z i‖ + T i := by
    have htriangle : ‖(a : ℂ) - Z i‖ ≤ |a| + ‖Z i‖ := by
      simpa using norm_sub_le (a : ℂ) (Z i)
    linarith [hpath i]
  have havg := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hw i))
  have hleft : (∑ i, w i * L) = L := by rw [← Finset.sum_mul, hsum, one_mul]
  have hright : (∑ i, w i * (1 + ‖Z i‖ + T i)) =
      1 + (∑ i, w i * ‖Z i‖) + (∑ i, w i * T i) := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, hsum]
  rw [hleft, hright] at havg
  have hbudget : L ≤ 1 + Real.sqrt (u ^ 2 + c * V / N) +
      c * Real.sqrt (V / N) := by linarith
  exact hbudget.trans (DerivativeChainPrivate.rb5_scalar N c u V hc hNc hV huV)
