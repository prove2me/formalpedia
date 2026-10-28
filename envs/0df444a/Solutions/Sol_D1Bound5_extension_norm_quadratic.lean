-- Prove2me | solution 1 for D1Bound5.extension_norm_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:37:37.098296+00:00
-- url     : https://prove2.me/submissions/6b6119dc-40f5-4b36-a3ba-7135abe3c180

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Regular_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The exact quadratic inequality (irregular-quadratic), with the
arithmetic input isolated as the lower bounds for the two extensions. -/
theorem _root_.solution (a b c u v : ℂ)
    (hs : u+v = 2*(a+b+(1+2*a*b)*c))
    (hp : u*v = regularDefect a b c) (hu : 1 ≤ ‖u‖) (hv : 1 ≤ ‖v‖) :
    0 ≤ ‖c‖^2-2*(‖1+2*a*b‖-‖a+b‖)*‖c‖ + ‖(a-b)^2-4‖ + 2*‖a+b‖+1 := by
  have hprod : ‖u‖+‖v‖ ≤ ‖regularDefect a b c‖+1 := by
    rw [← hp, norm_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hv)]
  have hdid : regularDefect a b c = c^2-2*(a+b)*c+((a-b)^2-4) := by
    unfold regularDefect
    ring
  have hd : ‖regularDefect a b c‖ ≤ ‖c‖^2+2*‖a+b‖*‖c‖+‖(a-b)^2-4‖ := by
    rw [hdid]
    have h1 := norm_add_le (c^2-2*(a+b)*c) ((a-b)^2-4)
    have h2 := norm_sub_le (c^2) (2*(a+b)*c)
    simp only [norm_pow, norm_mul, Complex.norm_ofNat] at h1 h2
    linarith
  have heq : (2 : ℂ)*(1+2*a*b)*c = u+v-2*(a+b) := by
    linear_combination -hs
  have ht : 2*‖1+2*a*b‖*‖c‖ ≤ ‖u‖+‖v‖+2*‖a+b‖ := by
    calc
      _ = ‖(2 : ℂ)*(1+2*a*b)*c‖ := by simp only [norm_mul, Complex.norm_two]
      _ = ‖u+v-2*(a+b)‖ := congrArg norm heq
      _ ≤ ‖u+v‖+‖(2 : ℂ)*(a+b)‖ := norm_sub_le _ _
      _ ≤ _ := by
        rw [norm_mul, Complex.norm_two]
        linarith [norm_add_le u v]
  nlinarith only [hprod, hd, ht]











end D1Bound5
end
