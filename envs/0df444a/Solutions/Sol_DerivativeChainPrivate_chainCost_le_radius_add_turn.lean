-- Prove2me | solution 1 for DerivativeChainPrivate.chainCost_le_radius_add_turn
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-19T05:08:54.741824+00:00
-- url     : https://prove2.me/submissions/75bf1fe6-7b89-4448-8c45-395c6ba5d67d

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial















end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate

theorem unit_phase_chord_le (x y : ℝ) :
    ‖Complex.exp (Complex.I * y) - Complex.exp (Complex.I * x)‖ ≤ |y - x| := by
  have heq : Complex.exp (Complex.I * y) - Complex.exp (Complex.I * x) =
      Complex.exp (Complex.I * x) * (Complex.exp (Complex.I * (y - x)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    ring
  rw [heq, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa only [Real.norm_eq_abs, Complex.ofReal_sub] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := y - x))



theorem polar_step_le_radial_add_turn (r s R x y : ℝ)
    (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ R) :
    ‖(s : ℂ) * Complex.exp (Complex.I * y) -
      (r : ℂ) * Complex.exp (Complex.I * x)‖ ≤ (s - r) + R * |y - x| := by
  have hsr : 0 ≤ s - r := sub_nonneg.mpr hrs
  have heq : (s : ℂ) * Complex.exp (Complex.I * y) -
      (r : ℂ) * Complex.exp (Complex.I * x) =
      ((s - r : ℝ) : ℂ) * Complex.exp (Complex.I * y) +
        (r : ℂ) * (Complex.exp (Complex.I * y) - Complex.exp (Complex.I * x)) := by
    push_cast
    ring
  rw [heq]
  calc
    _ ≤ ‖((s - r : ℝ) : ℂ) * Complex.exp (Complex.I * y)‖ +
        ‖(r : ℂ) * (Complex.exp (Complex.I * y) - Complex.exp (Complex.I * x))‖ := norm_add_le _ _
    _ = (s - r) + r * ‖Complex.exp (Complex.I * y) - Complex.exp (Complex.I * x)‖ := by
      rw [norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hsr, abs_of_nonneg hr, mul_one]
    _ ≤ (s - r) + R * |y - x| := by
      have hc := unit_phase_chord_le x y
      have hrr : r ≤ R := hrs.trans hs
      nlinarith [abs_nonneg (y - x)]



end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution {n : ℕ} (hn : 1 ≤ n)
    (r theta : ℕ → ℝ) (R alpha : ℝ) (hR : 0 ≤ R)
    (hr : ∀ i < n, 0 ≤ r i) (hmono : ∀ i < n - 1, r i ≤ r (i + 1))
    (hradius : ∀ i < n, r i ≤ R)
    (hturn : (∑ i ∈ Finset.range (n - 1), |theta (i + 1) - theta i|) ≤ alpha) :
    chainCost (fun i : Fin n => (r i.val : ℂ) * Complex.exp (Complex.I * theta i.val)) ≤
      R - r 0 + R * alpha := by
  calc
    _ ≤ ∑ i : Fin (n - 1), ((r (i.val + 1) - r i.val) +
        R * |theta (i.val + 1) - theta i.val|) := by
      apply Finset.sum_le_sum
      intro i _
      exact polar_step_le_radial_add_turn _ _ _ _ _ (hr _ (by omega))
        (hmono _ i.isLt) (hradius _ (by omega))
    _ = r (n - 1) - r 0 +
        R * (∑ i ∈ Finset.range (n - 1), |theta (i + 1) - theta i|) := by
      rw [Fin.sum_univ_eq_sum_range (fun i => (r (i + 1) - r i) +
        R * |theta (i + 1) - theta i|), Finset.sum_add_distrib,
        Finset.sum_range_sub r (n - 1), ← Finset.mul_sum]
    _ ≤ R - r 0 + R * alpha := by
      have he := hradius (n - 1) (by omega)
      nlinarith
