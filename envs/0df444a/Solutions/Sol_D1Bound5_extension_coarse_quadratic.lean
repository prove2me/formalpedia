-- Prove2me | solution 1 for D1Bound5.extension_coarse_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:13.770246+00:00
-- url     : https://prove2.me/submissions/178caae8-c614-48bd-80c2-4a9e54081faf

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
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_extension_norm_quadratic

section
open scoped NumberField
open Module

namespace D1Bound5



/-- The coarser quadratic used to exclude B <= C <= 2AB. -/
theorem _root_.solution (a b c u v : ℂ)
    (hs : u+v = 2*(a+b+(1+2*a*b)*c))
    (hp : u*v = regularDefect a b c) (hu : 1 ≤ ‖u‖) (hv : 1 ≤ ‖v‖) :
    0 ≤ (‖a‖+‖b‖+‖c‖+1)^2+4-4*‖a‖*‖b‖*‖c‖ := by
  have hq := extension_norm_quadratic a b c u v hs hp hu hv
  have hP := norm_add_le a b
  have hH : 2*‖a‖*‖b‖ ≤ ‖1+2*a*b‖+1 := by
    calc
      _ = ‖(2 : ℂ)*a*b‖ := by simp only [norm_mul, Complex.norm_two]
      _ = ‖(1+2*a*b)-1‖ := by congr 1; ring
      _ ≤ ‖1+2*a*b‖+1 := by simpa only [norm_one] using norm_sub_le (1+2*a*b) 1
  have hsq : ‖a-b‖^2 ≤ (‖a‖+‖b‖)^2 := by
    have h := mul_nonneg (sub_nonneg.mpr (norm_sub_le a b))
      (add_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b)) (norm_nonneg (a-b)))
    nlinarith only [h]
  have hT : ‖(a-b)^2-4‖ ≤ (‖a‖+‖b‖)^2+4 := by
    have h := norm_sub_le ((a-b)^2) (4 : ℂ)
    simp only [norm_pow, Complex.norm_ofNat] at h
    linarith
  have hPC := mul_le_mul_of_nonneg_right hP (norm_nonneg c)
  have hHC := mul_le_mul_of_nonneg_right hH (norm_nonneg c)
  nlinarith only [hq, hP, hT, hPC, hHC]









end D1Bound5
end
