-- Prove2me | solution 1 for D1Bound5.full_ring_small_pair_descent
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:30:23.389709+00:00
-- url     : https://prove2.me/submissions/92d74f3c-c3e5-4da4-b22e-e68d539d3e4d

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DescentAlgebra_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_complex_small_anchor_descent
import Theorems.Thm_D1Bound5_full_ring_descent_denominator_norm_sq_ge_seven
import Theorems.Thm_D1Bound5_mutate_roots
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The complete norm-decreasing small-pair mutation in the full ring of
integers. All input roots are arbitrary fixed roots; the output is one of
the two canonical sign neighbors computed from those same roots. Zero
output roots and a zero output extension are permitted. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a b z r0 r s : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a*b+1 ≠ 0)
    (h0 : r0^2 = a*b+1) (hr : r^2 = a*z+1) (hs : s^2 = b*z+1)
    (hA : ‖phi (a : K)‖ < 3) (hB : ‖phi (b : K)‖ < 3)
    (hZ : 33 ≤ ‖phi (z : K)‖) :
    ∃ w : 𝓞 K,
      (w = mutate a b z r0 r s ∨ w = mutate a b z r0 r (-s)) ∧
      (∃ r' : 𝓞 K, r'^2 = a*w+1) ∧
      (∃ s' : 𝓞 K, s'^2 = b*w+1) ∧
      ‖phi (w : K)‖ < ‖phi (z : K)‖/5+26 ∧
      ‖phi (w : K)‖ < ‖phi (z : K)‖ ∧
      ‖phi (w : K)‖^2 < ‖phi (z : K)‖^2 := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have h0C : (f r0)^2 = f a*f b+1 := by
    simpa only [map_pow, map_mul, map_add, map_one] using congrArg f h0
  have hrC : (f r)^2 = f a*f z+1 := by
    simpa only [map_pow, map_mul, map_add, map_one] using congrArg f hr
  have hsC : (f s)^2 = f b*f z+1 := by
    simpa only [map_pow, map_mul, map_add, map_one] using congrArg f hs
  have hp : 1 ≤ ‖f a*f b‖ := by
    have h := one_le_norm_integer hK phi (mul_ne_zero ha hb : a*b ≠ 0)
    change 1 ≤ ‖f (a*b)‖ at h
    simpa only [map_mul] using h
  have hhyper : 7 ≤ ‖2*f a*f b+1‖^2 :=
    full_ring_descent_denominator_norm_sq_ge_seven hK phi a b r0 ha hb hab h0
  have hstep : ‖f z‖/5+26 < ‖f z‖ := by
    change ‖phi (z : K)‖/5+26 < ‖phi (z : K)‖
    linarith only [hZ]
  have hmap (s' : 𝓞 K) : f (mutate a b z r0 r s') =
      mutate (f a) (f b) (f z) (f r0) (f r) (f s') := by
    simp only [mutate,map_add,map_mul,map_one,map_ofNat]
  have finish (w : 𝓞 K)
      (hw : w = mutate a b z r0 r s ∨ w = mutate a b z r0 r (-s))
      (hwr : ∃ r' : 𝓞 K, r'^2 = a*w+1)
      (hws : ∃ s' : 𝓞 K, s'^2 = b*w+1)
      (hbound : ‖f w‖ < ‖f z‖/5+26) :
      ∃ w : 𝓞 K,
        (w = mutate a b z r0 r s ∨ w = mutate a b z r0 r (-s)) ∧
        (∃ r' : 𝓞 K, r'^2 = a*w+1) ∧
        (∃ s' : 𝓞 K, s'^2 = b*w+1) ∧
        ‖phi (w : K)‖ < ‖phi (z : K)‖/5+26 ∧
        ‖phi (w : K)‖ < ‖phi (z : K)‖ ∧
        ‖phi (w : K)‖^2 < ‖phi (z : K)‖^2 := by
    have hdec : ‖f w‖ < ‖f z‖ := hbound.trans hstep
    have hsq : ‖f w‖^2 < ‖f z‖^2 := by
      nlinarith only [mul_pos (sub_pos.mpr hdec)
        (add_pos_of_pos_of_nonneg
          (lt_of_le_of_lt (norm_nonneg (f w)) hdec) (norm_nonneg (f w)))]
    exact ⟨w, hw, hwr, hws, hbound, hdec, hsq⟩
  rcases complex_small_anchor_descent (f a) (f b) (f z) (f r0) (f r) (f s)
    h0C hrC hsC hA hB hp hZ hhyper with hplus | hminus
  · have hroots := mutate_roots a b z r0 r s h0 hr hs
    apply finish (mutate a b z r0 r s) (Or.inl rfl)
      ⟨r0*r+a*s, hroots.1⟩ ⟨b*r+r0*s, hroots.2⟩
    simpa only [hmap] using hplus
  · have hsneg : (-s)^2 = b*z+1 := by simpa only [neg_sq] using hs
    have hroots := mutate_roots a b z r0 r (-s) h0 hr hsneg
    apply finish (mutate a b z r0 r (-s)) (Or.inr rfl)
      ⟨r0*r+a*(-s), hroots.1⟩ ⟨b*r+r0*(-s), hroots.2⟩
    simpa only [hmap, map_neg] using hminus

end D1Bound5
end
