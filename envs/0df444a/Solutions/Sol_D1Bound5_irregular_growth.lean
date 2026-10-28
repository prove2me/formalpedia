-- Prove2me | solution 1 for D1Bound5.irregular_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:46:28.155021+00:00
-- url     : https://prove2.me/submissions/f1b9047a-f692-4834-8720-c694c4b3ea8a

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
import Theorems.Thm_D1Bound5_extension_coarse_quadratic
import Theorems.Thm_D1Bound5_extension_product
import Theorems.Thm_D1Bound5_growth_quadratic_negative
import Theorems.Thm_D1Bound5_irregular_extensions_ne_zero
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5











/-- Lemma irregular-growth in the full ring of every imaginary quadratic
field. Ordered moduli may be equal. -/
theorem _root_.solution {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K] (hK : finrank ℚ K = 2) (φ : K →+* ℂ)
    (a b c r s t : 𝓞 K) (hr : r^2 = a*b+1) (hs : s^2 = a*c+1)
    (ht : t^2 = b*c+1) (hi : regularDefect a b c ≠ 0)
    (hA : 3 ≤ ‖φ (a : K)‖) (hAB : ‖φ (a : K)‖ ≤ ‖φ (b : K)‖)
    (hBC : ‖φ (b : K)‖ ≤ ‖φ (c : K)‖) :
    2*‖φ (a : K)‖*‖φ (b : K)‖ < ‖φ (c : K)‖ := by
  let f := φ.comp (algebraMap (𝓞 K) K)
  let u := a+b+c+2*a*b*c+2*r*s*t
  let v := a+b+c+2*a*b*c-2*r*s*t
  have hn := irregular_extensions_ne_zero a b c r s t hr hs ht hi
  have hu : 1 ≤ ‖f u‖ := one_le_norm_integer hK φ hn.1
  have hv : 1 ≤ ‖f v‖ := one_le_norm_integer hK φ hn.2
  have hp : f u*f v = regularDefect (f a) (f b) (f c) := by
    have h := congrArg f (extension_product a b c r s t hr hs ht)
    simpa only [u, v, regularDefect, map_mul, map_add, map_sub, map_pow, map_ofNat] using h
  have hsum : f u+f v = 2*(f a+f b+(1+2*f a*f b)*f c) := by
    simp only [u, v, map_add, map_sub, map_mul, map_ofNat]
    ring
  have hq := extension_coarse_quadratic (f a) (f b) (f c) (f u) (f v) hsum hp hu hv
  by_contra h
  have hC : ‖f c‖ ≤ 2*‖f a‖*‖f b‖ := le_of_not_gt h
  have hneg := growth_quadratic_negative ‖f a‖ ‖f b‖ ‖f c‖ hA hAB hBC hC
  linarith

end D1Bound5
end
