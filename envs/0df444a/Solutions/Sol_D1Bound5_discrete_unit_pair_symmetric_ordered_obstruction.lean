-- Prove2me | solution 1 for D1Bound5.discrete_unit_pair_symmetric_ordered_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:27:43.146972+00:00
-- url     : https://prove2.me/submissions/21562c28-6910-4827-ac23-6f3063ae8af0

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
import Theorems.Thm_D1Bound5_unit_pair_symmetric_complex_obstruction
import Theorems.Thm_D1Bound5_unit_pair_symmetric_factorization

section
open scoped NumberField
open Module

namespace D1Bound5





/-- In a discrete complex ring image, the four square conditions of the
ordered symmetric-five argument are impossible once both moduli are at
least three. In particular no root-nonvanishing hypothesis is needed. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (hdiscrete : ∀ z : R, z ≠ 0 → 1 ≤ ‖f z‖)
    (a b x y v w : R) (hA : 3 ≤ ‖f a‖) (hAB : ‖f a‖ ≤ ‖f b‖)
    (hx : x ^ 2 = 1 - b) (hy : y ^ 2 = 1 + b)
    (hv : v ^ 2 = 1 - a * b) (hw : w ^ 2 = 1 + a * b) : False := by
  let G : R := 2 * a ^ 2 * b ^ 2 - a ^ 2 - 1
  let J : R := 2 * a * x * y * v * w
  have hid : (G - J) * (G + J) = (a ^ 2 - 1) ^ 2 :=
    unit_pair_symmetric_factorization a b x y v w hx hy hv hw
  have himage : (f G - f J) * (f G + f J) = ((f a) ^ 2 - 1) ^ 2 := by
    simpa only [map_mul, map_sub, map_add, map_pow, map_one] using congrArg f hid
  have ha1 : (f a) ^ 2 ≠ 1 := by
    intro h
    have hn := congrArg norm h
    simp only [norm_pow, norm_one] at hn
    nlinarith only [hA, hn, sq_nonneg (‖f a‖ - 3)]
  have hrhs : ((f a) ^ 2 - 1) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (sub_ne_zero.mpr ha1)
  have hm : G - J ≠ 0 := by
    intro h
    have hz : f G - f J = 0 := by
      simpa only [map_sub, map_zero] using congrArg f h
    rw [hz, zero_mul] at himage
    exact hrhs himage.symm
  have hp : G + J ≠ 0 := by
    intro h
    have hz : f G + f J = 0 := by
      simpa only [map_add, map_zero] using congrArg f h
    rw [hz, mul_zero] at himage
    exact hrhs himage.symm
  apply unit_pair_symmetric_complex_obstruction (f a) (f b) (f G) (f J) hA hAB
  · simp only [G, map_sub, map_mul, map_pow, map_ofNat, map_one]
  · exact himage
  · simpa only [map_sub] using hdiscrete (G - J) hm
  · simpa only [map_add] using hdiscrete (G + J) hp





end D1Bound5
end
