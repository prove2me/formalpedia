-- Prove2me | solution 1 for D1Bound5.finitePolynomial_height_scalar
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:33:19.971431+00:00
-- url     : https://prove2.me/submissions/c6869df1-0456-49c0-8ab8-3930de48f090

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5





theorem finitePolynomial_power_majorization (T : ℝ) (hT : 1000 ≤ T)
    (k ell : ℕ) (hell : ell ≤ k) : T^ell ≤ T^k/(1000 : ℝ)^(k-ell) := by
  have hT0 : 0 ≤ T := by linarith only [hT]
  apply (le_div_iff₀ (by positivity)).mpr
  have hp : (1000 : ℝ)^(k-ell) ≤ T^(k-ell) := by gcongr
  calc
    T^ell*(1000 : ℝ)^(k-ell) ≤ T^ell*T^(k-ell) :=
      mul_le_mul_of_nonneg_left hp (pow_nonneg hT0 _)
    _ = T^k := by rw [← pow_add,Nat.add_sub_of_le hell]

/-- A rational computation on the actual coefficient vector supplies the
strict height margin for every T≥1000. This avoids weakening the constants
by combining coordinatewise maxima from different rows. -/
theorem _root_.solution (k : ℕ) (v : Fin (k+1) → ℝ)
    (hv : ∀ ell, 0 ≤ v ell) (M T : ℝ) (hT : 1000 ≤ T)
    (hslack : (101/100 : ℝ)*(∑ ell, v ell/(1000 : ℝ)^(k-(ell : ℕ))) < M) :
    (101/100 : ℝ)*(∑ ell, v ell*T^(ell : ℕ)) < M*T^k := by
  have hT0 : 0 < T := by linarith only [hT]
  have hsum : (∑ ell, v ell*T^(ell : ℕ)) ≤
      ∑ ell, (v ell/(1000 : ℝ)^(k-(ell : ℕ)))*T^k := by
    apply Finset.sum_le_sum
    intro ell hell
    have hh := mul_le_mul_of_nonneg_left
      (finitePolynomial_power_majorization T hT k ell.val (by omega)) (hv ell)
    convert hh using 1 <;> ring
  calc
    _ ≤ (101/100 : ℝ)*(∑ ell, (v ell/(1000 : ℝ)^(k-(ell : ℕ)))*T^k) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = ((101/100 : ℝ)*(∑ ell, v ell/(1000 : ℝ)^(k-(ell : ℕ))))*T^k := by
      rw [← Finset.sum_mul]
      ring
    _ < M*T^k := mul_lt_mul_of_pos_right hslack (pow_pos hT0 _)

end D1Bound5
end
