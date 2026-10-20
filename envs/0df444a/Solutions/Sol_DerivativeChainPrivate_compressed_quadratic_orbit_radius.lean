-- Prove2me | solution 1 for DerivativeChainPrivate.compressed_quadratic_orbit_radius
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-19T05:03:47.798986+00:00
-- url     : https://prove2.me/submissions/dfc65ac3-e1c6-4303-ba28-69f47d7336eb

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









end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution (A B : ℝ) (hdisc : A ^ 2 < 4 * B)
    (d : ℕ) (w : ℂ)
    (hroot : (w ^ d) ^ 2 + (A : ℂ) * w ^ d + (B : ℂ) = 0) :
    ‖w‖ ^ (2 * d) = B := by
  let u := w ^ d
  have hre := congrArg Complex.re hroot
  have him := congrArg Complex.im hroot
  change (u ^ 2 + (A : ℂ) * u + (B : ℂ)).re = 0 at hre
  change (u ^ 2 + (A : ℂ) * u + (B : ℂ)).im = 0 at him
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.mul_im,
    add_zero] at hre him
  have hni : u.im ≠ 0 := by
    intro hz
    rw [hz] at hre
    nlinarith [sq_nonneg (2 * u.re + A)]
  have hlinear : 2 * u.re + A = 0 := by
    have hp : u.im * (2 * u.re + A) = 0 := by nlinarith [him]
    exact (mul_eq_zero.mp hp).resolve_left hni
  have hn : ‖u‖ ^ 2 = B := by
    have hnorm := Complex.sq_norm_sub_sq_re u
    have hprod : (2 * u.re + A) * u.re = 0 := by rw [hlinear]; ring
    nlinarith [hre]
  rw [show 2 * d = d * 2 by omega, pow_mul, ← norm_pow]
  exact hn
