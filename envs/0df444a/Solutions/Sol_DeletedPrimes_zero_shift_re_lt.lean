-- Prove2me | solution 1 for DeletedPrimes.zero_shift_re_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:20:19.352548+00:00
-- url     : https://prove2.me/submissions/90c59b17-f0a3-4f43-83ed-e6943cc6d8a4

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {α : ℝ} {s ρ : ℂ} (hα1 : α < 1) (hρ : ρ.re ≤ 1 / 2) (h : s + 1 - α = ρ) :
    s.re < α / 2 := by
  have := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.ofReal_re] at this
  linarith
end DeletedPrimes
