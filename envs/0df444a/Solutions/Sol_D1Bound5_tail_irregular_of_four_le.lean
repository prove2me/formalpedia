-- Prove2me | solution 1 for D1Bound5.tail_irregular_of_four_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:19:05.99015+00:00
-- url     : https://prove2.me/submissions/77b20db8-edf7-4e5a-a2c0-a0b647932b1f

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Regular_Definitions
import Theorems.Thm_D1Bound5_no_regular_large_tail_core
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5



/-- The C>=4 branch of lem:tail-irregular in the full ring of integers
of every imaginary quadratic field. No root is assumed to be nonzero. -/
theorem _root_.solution {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K] (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a b c d : 𝓞 K) (ha : a ≠ 0)
    (hab : ∃ u : 𝓞 K, u^2 = a*b+1) (hac : ∃ v : 𝓞 K, v^2 = a*c+1)
    (had : ∃ w : 𝓞 K, w^2 = a*d+1) (hbc : ∃ r : 𝓞 K, r^2 = b*c+1)
    (hAB : ‖phi (a : K)‖ ≤ ‖phi (b : K)‖) (hB : 3 ≤ ‖phi (b : K)‖)
    (hC : 4 ≤ ‖phi (c : K)‖) (hCD : ‖phi (c : K)‖ ≤ ‖phi (d : K)‖) :
    regularDefect b c d ≠ 0 := by
  intro hreg
  obtain ⟨u,hu⟩ := hab
  obtain ⟨v,hv⟩ := hac
  obtain ⟨w,hw⟩ := had
  obtain ⟨r,hr⟩ := hbc
  have hp : (d-b-c-2*r)*(d-b-c+2*r) = 0 := by
    unfold regularDefect at hreg
    linear_combination hreg-4*hr
  let f := phi.comp (algebraMap (𝓞 K) K)
  have hn (s : 𝓞 K) (hs : s ≠ 0) : 1 ≤ ‖f s‖ := one_le_norm_integer hK phi hs
  rcases mul_eq_zero.mp hp with h | h
  · have hd : d = b+c+2*r := by linear_combination h
    exact no_regular_large_tail_core f hn a b c d r u v w hr hu hv hw hd
      (hn a ha) hB hC hAB hCD
  · have hd : d = b+c+2*(-r) := by linear_combination h
    have hr' : (-r)^2 = b*c+1 := by simpa only [neg_sq] using hr
    exact no_regular_large_tail_core f hn a b c d (-r) u v w hr' hu hv hw hd
      (hn a ha) hB hC hAB hCD




end D1Bound5
end
