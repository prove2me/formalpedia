-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.tail_irregular_and_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:28:54.302988+00:00
-- url     : https://prove2.me/submissions/bd656427-151b-499d-a803-c0d3a23d8c20

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_Regular_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_tail_irregular_and_growth_of_four_le
import Theorems.Thm_D1Bound5_IsD1Tuple_tail_irregular_of_lt_four
import Theorems.Thm_D1Bound5_irregular_growth

section
open scoped NumberField
open Module

namespace D1Bound5



/-- Complete tail-irregularity and growth lemma, without the auxiliary
C>=4 restriction. Every zero-square, half-integral, and modulus-tie case remains. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 4 → 𝓞 K) (ht : IsD1Tuple t)
    (hmon : Monotone (fun i => ‖phi (t i : K)‖))
    (hB : 3 ≤ ‖phi (t 1 : K)‖) :
    regularDefect (t 1) (t 2) (t 3) ≠ 0 ∧
      2*‖phi (t 1 : K)‖*‖phi (t 2 : K)‖ < ‖phi (t 3 : K)‖ := by
  by_cases hC : 4 ≤ ‖phi (t 2 : K)‖
  · exact IsD1Tuple.tail_irregular_and_growth_of_four_le hK phi t ht hmon hB hC
  · have hirr := IsD1Tuple.tail_irregular_of_lt_four hK phi t ht hmon hB (lt_of_not_ge hC)
    obtain ⟨r,hr⟩ := ht.2.2 1 2 (by decide)
    obtain ⟨s,hs⟩ := ht.2.2 1 3 (by decide)
    obtain ⟨v,hv⟩ := ht.2.2 2 3 (by decide)
    exact ⟨hirr, irregular_growth hK phi (t 1) (t 2) (t 3) r s v
      (by simpa only [pow_two] using hr) (by simpa only [pow_two] using hs)
      (by simpa only [pow_two] using hv) hirr hB
      (hmon (by decide : (1 : Fin 4) ≤ 2)) (hmon (by decide : (2 : Fin 4) ≤ 3))⟩

end D1Bound5
end
