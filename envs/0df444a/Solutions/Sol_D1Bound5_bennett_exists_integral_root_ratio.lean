-- Prove2me | solution 1 for D1Bound5.bennett_exists_integral_root_ratio
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:53:09.236084+00:00
-- url     : https://prove2.me/submissions/f9100796-25e4-43fe-98fc-d8347872197b

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
import Theorems.Thm_D1Bound5_bennett_exists_sign_root_error
import Theorems.Thm_D1Bound5_bennett_root_ratio_square_error

section
namespace D1Bound5





/-- The source-ring witness is a sign of the existing product of integral
roots. It is chosen once, independently of the later matrix row. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a c d z r v : R) (θ : ℂ)
    (ha : f a ≠ 0) (hc : f c ≠ 0) (hz : f z ≠ 0) (hθ0 : θ ≠ 0)
    (hr : r ^ 2 = a * c + 1) (hv : v ^ 2 = a * d + 1)
    (hzsq : z ^ 2 = c * d + 1) (hθ : θ ^ 2 = 1 + 1 / (f a * f c)) :
    ∃ s : R, (s = r * v ∨ s = -(r * v)) ∧
      0 ≤ ((f s / (f a * f z)) / θ).re ∧
      ‖θ - f s / (f a * f z)‖ ≤
        ‖θ‖ * ‖f c - f a‖ / (‖f a‖ * ‖f z‖ ^ 2) := by
  have hrC : (f r) ^ 2 = f a * f c + 1 := by
    simpa only [map_pow, map_mul, map_add, map_one] using congrArg f hr
  have hvC : (f v) ^ 2 = f a * f d + 1 := by
    simpa only [map_pow, map_mul, map_add, map_one] using congrArg f hv
  have hzC : (f z) ^ 2 = f c * f d + 1 := by
    simpa only [map_pow, map_mul, map_add, map_one] using congrArg f hzsq
  have hsquare := bennett_root_ratio_square_error (f a) (f c) (f d) (f z)
    (f r) (f v) θ ha hc hz hrC hvC hzC hθ
  obtain ⟨w, hw, hRe, herr⟩ := bennett_exists_sign_root_error
    (f r * f v / (f a * f z)) θ hθ0
  have hnorm : ‖(f r * f v / (f a * f z)) ^ 2 - θ ^ 2‖ / ‖θ‖ =
      ‖θ‖ * ‖f c - f a‖ / (‖f a‖ * ‖f z‖ ^ 2) := by
    rw [hsquare, norm_div, norm_mul, norm_pow, norm_mul, norm_pow]
    field_simp [norm_ne_zero_iff.mpr hθ0, norm_ne_zero_iff.mpr ha, norm_ne_zero_iff.mpr hz]
    <;> ring
  rw [hnorm] at herr
  rcases hw with hw | hw
  · refine ⟨r * v, Or.inl rfl, ?_, ?_⟩
    · simpa only [hw, map_mul] using hRe
    · simpa only [hw, map_mul] using herr
  · refine ⟨-(r * v), Or.inr rfl, ?_, ?_⟩
    · simpa only [hw, map_neg, map_mul, neg_div] using hRe
    · simpa only [hw, map_neg, map_mul, neg_div] using herr





end D1Bound5
end
