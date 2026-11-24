-- Prove2me | solution 1 for DeletedPrimes.zero_double_shift_re_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:20:31.356833+00:00
-- url     : https://prove2.me/submissions/4acd87b9-cd6c-4c99-b422-940d80af4b27

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {α : ℝ} {s ρ : ℂ} (hρ : ρ.re ≤ 1 / 2) (h : 2 * s + 1 - α = ρ) :
    s.re < α / 2 := by
  have := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re,
    Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at this
  linarith
end DeletedPrimes
