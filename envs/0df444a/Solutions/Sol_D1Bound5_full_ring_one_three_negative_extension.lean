-- Prove2me | solution 1 for D1Bound5.full_ring_one_three_negative_extension
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:49:56.214896+00:00
-- url     : https://prove2.me/submissions/7e753e7c-d581-4eea-9f5f-f7bb8d72c7b1

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_D1Bound5_full_ring_nonpositive_integer_squares_common_parameter
import Theorems.Thm_D1Bound5_full_ring_one_three_common_extension_is_integer
import Theorems.Thm_D1Bound5_full_ring_positive_integer_square
import Theorems.Thm_D1Bound5_one_three_negative_integer_restriction
import Theorems.Thm_D1Bound5_one_three_positive_eight_dvd

section
open scoped NumberField
open Module

namespace D1Bound5















/-- A positive common extension cannot coexist with a negative one when
all nonpositive square values use the same imaginary quadratic parameter. -/
theorem one_three_mixed_sign_obstruction {p x w : ℤ}
    (hp : 8 ∣ p) (hw : p*x-1=2*w^2) : False := by
  obtain ⟨t,rfl⟩ := hp
  have he : 8*t*x-1 = 2*(w^2) := hw
  have hmul : 8*t*x = 2*(4*t*x) := by ring
  omega






/-- Among extensions of 1 and 3, a negative one forces all other
nonzero compatible entries to be negative odd rational integers. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) {n : ℤ} (hn : n < 0)
    (hnr : ∃ r : 𝓞 K, r*r = (n : 𝓞 K)+1)
    (hns : ∃ s : 𝓞 K, s*s = 3*(n : 𝓞 K)+1)
    {z : 𝓞 K} (hz : z ≠ 0)
    (hzr : ∃ r : 𝓞 K, r*r = z+1)
    (hzs : ∃ s : 𝓞 K, s*s = 3*z+1)
    (hzn : z = (n : 𝓞 K) ∨ ∃ r : 𝓞 K, r*r = z*(n : 𝓞 K)+1) :
    ∃ p : ℤ, z=(p : 𝓞 K) ∧ p<0 ∧ p%2=1 := by
  obtain ⟨d,hd,hparam⟩ := full_ring_nonpositive_integer_squares_common_parameter hK
  obtain ⟨rfl,hnodd⟩ := one_three_negative_integer_restriction d hd hparam hn hnr hns
  obtain ⟨p,rfl⟩ := full_ring_one_three_common_extension_is_integer hK hzr hzs
  have hp0 : p ≠ 0 := by intro hp; simpa [hp] using hz
  rcases lt_or_gt_of_ne hp0 with hp | hp
  · exact ⟨p,rfl,hp,(one_three_negative_integer_restriction 2 (by norm_num)
      hparam hp hzr hzs).2⟩
  · obtain ⟨r,hr⟩ := full_ring_positive_integer_square hK (m := p+1)
      (by omega) (by simpa using hzr)
    obtain ⟨s,hs⟩ := full_ring_positive_integer_square hK (m := 3*p+1)
      (by omega) (by simpa using hzs)
    have hp8 := one_three_positive_eight_dvd hr hs
    have hsq : ∃ r : 𝓞 K, r*r = ((p*n+1 : ℤ) : 𝓞 K) := by
      rcases hzn with he | he
      · have he' : p=n := Int.cast_injective he
        omega
      · simpa using he
    have hpn : p*n+1 ≤ 0 := by nlinarith
    obtain ⟨w,hw⟩ := hparam (p*n+1) hpn hsq
    exact False.elim (one_three_mixed_sign_obstruction hp8
      (x := -n) (w := w) (by nlinarith [hw]))








end D1Bound5
end
