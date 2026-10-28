-- Prove2me | solution 1 for D1Bound5.finitePolynomial_two_columns_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:44:40.521994+00:00
-- url     : https://prove2.me/submissions/ed4f435b-f36c-4a9a-bcc4-8506a712f06f

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
import Theorems.Thm_D1Bound5_finitePolynomial_norm_le

section
namespace D1Bound5



theorem _root_.solution (k d0 : ℕ)
    (p : Fin 2 → Fin (k+1) → ℂ) (v : Fin (k+1) → ℝ) (c : ℂ) (Y : ℝ)
    (hcoeff : ∀ ell, ‖p 0 ell‖+‖p 1 ell‖ ≤ v ell*Y^(d0+(ell : ℕ))) :
    ‖∑ ell, p 0 ell*c^(ell : ℕ)‖+‖∑ ell, p 1 ell*c^(ell : ℕ)‖ ≤
      Y^d0*∑ ell, v ell*(Y*‖c‖)^(ell : ℕ) := by
  calc
    _ ≤ (∑ ell, ‖p 0 ell‖*‖c‖^(ell : ℕ))+
        ∑ ell, ‖p 1 ell‖*‖c‖^(ell : ℕ) :=
      add_le_add (finitePolynomial_norm_le k (p 0) c) (finitePolynomial_norm_le k (p 1) c)
    _ = ∑ ell, (‖p 0 ell‖+‖p 1 ell‖)*‖c‖^(ell : ℕ) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ell hell
      ring
    _ ≤ ∑ ell, (v ell*Y^(d0+(ell : ℕ)))*‖c‖^(ell : ℕ) := by
      apply Finset.sum_le_sum
      intro ell hell
      exact mul_le_mul_of_nonneg_right (hcoeff ell) (pow_nonneg (norm_nonneg c) _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell hell
      rw [pow_add,mul_pow]
      ring





end D1Bound5
end
