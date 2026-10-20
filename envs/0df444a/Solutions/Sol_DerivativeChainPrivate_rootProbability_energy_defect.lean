-- Prove2me | solution 1 for DerivativeChainPrivate.rootProbability_energy_defect
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-17T18:46:42.242032+00:00
-- url     : https://prove2.me/submissions/fdff2f70-4d08-4f3c-b97d-a8674b5e7baa

import Definitions.Def_DerivativeChain_root_probability
import Theorems.Thm_DerivativeChain_rootProbability_centered_increment
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open scoped BigOperators Polynomial
set_option autoImplicit false

namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate in
theorem solution (P : ℂ[X]) (hP : 0 < P.degree)
    (z : ℂ) (hz : P.derivative.eval z = 0) :
    (∑ w : P.roots.toFinset, DerivativeChain.rootProbability P z w *
      (‖(w : ℂ) - z‖ ^ 2 - ‖(w : ℂ)‖ ^ 2 + ‖z‖ ^ 2)) = 0 := by
  have hnorm : ∀ a : ℂ, ‖a‖ ^ 2 = a.re * a.re + a.im * a.im := fun a =>
    (RCLike.normSq_eq_def' a).symm.trans (RCLike.normSq_apply a)
  have hdefect : ∀ a : ℂ,
      ‖a - z‖ ^ 2 - ‖a‖ ^ 2 + ‖z‖ ^ 2 =
        -2 * (z.re * (a - z).re + z.im * (a - z).im) := by
    intro a
    rw [hnorm (a - z), hnorm a, hnorm z, Complex.sub_re, Complex.sub_im]
    ring
  have hcenter : (∑ w : P.roots.toFinset, DerivativeChain.rootProbability P z w *
      (z.re * ((w : ℂ) - z).re + z.im * ((w : ℂ) - z).im)) = 0 := by
    simpa only [sub_zero] using DerivativeChain.rootProbability_centered_increment hP hz 0
  calc
    _ = -2 * (∑ w : P.roots.toFinset, DerivativeChain.rootProbability P z w *
        (z.re * ((w : ℂ) - z).re + z.im * ((w : ℂ) - z).im)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [hdefect]
      ring
    _ = 0 := by rw [hcenter, mul_zero]
