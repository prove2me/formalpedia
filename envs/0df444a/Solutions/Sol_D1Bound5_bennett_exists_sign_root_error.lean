-- Prove2me | solution 1 for D1Bound5.bennett_exists_sign_root_error
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:45:36.449628+00:00
-- url     : https://prove2.me/submissions/e562c73b-8dcf-428d-986f-e4329d8c2d2b

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
namespace D1Bound5

/-- One fixed sign gives the elementary root error bound relative to any
nonzero complex target. The chosen sign is retained in the conclusion. -/
theorem _root_.solution (t θ : ℂ) (hθ : θ ≠ 0) :
    ∃ v : ℂ, (v = t ∨ v = -t) ∧
      0 ≤ (v / θ).re ∧ ‖θ - v‖ ≤ ‖t ^ 2 - θ ^ 2‖ / ‖θ‖ := by
  have existsSign : ∃ v : ℂ, (v = t ∨ v = -t) ∧ 0 ≤ (v / θ).re := by
    by_cases h : 0 ≤ (t / θ).re
    · exact ⟨t, Or.inl rfl, h⟩
    · refine ⟨-t, Or.inr rfl, ?_⟩
      simp only [neg_div, Complex.neg_re]
      linarith
  obtain ⟨v, hv, hRe⟩ := existsSign
  have hv2 : v ^ 2 = t ^ 2 := by rcases hv with h | h <;> rw [h] <;> simp
  have hunit : 1 ≤ ‖v / θ + 1‖ := by
    have hh := Complex.re_le_norm (v / θ + 1)
    simp only [Complex.add_re, Complex.one_re] at hh
    linarith
  have hscale : v + θ = θ * (v / θ + 1) := by field_simp [hθ]
  have hplus : ‖θ‖ ≤ ‖v + θ‖ := by
    rw [hscale, norm_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hunit (norm_nonneg θ)
  have hprod : ‖θ - v‖ * ‖v + θ‖ = ‖t ^ 2 - θ ^ 2‖ := by
    rw [← norm_mul]
    have hid : (θ - v) * (v + θ) = -(t ^ 2 - θ ^ 2) := by
      calc
        _ = -(v ^ 2 - θ ^ 2) := by ring
        _ = _ := by rw [hv2]
    rw [hid, norm_neg]
  refine ⟨v, hv, hRe, (le_div_iff₀ (norm_pos_iff.mpr hθ)).mpr ?_⟩
  exact (mul_le_mul_of_nonneg_left hplus (norm_nonneg _)).trans_eq hprod









end D1Bound5
end
