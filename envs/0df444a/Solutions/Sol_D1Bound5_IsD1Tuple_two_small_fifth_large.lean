-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.two_small_fifth_large
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:10:52.362216+00:00
-- url     : https://prove2.me/submissions/b8d91c6c-8479-4e01-abd8-8e63e3df1be2

import Init
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_IsD1Tuple
import Theorems.Thm_D1Bound5_IsD1Tuple_properCommonExtension_first_two
import Theorems.Thm_D1Bound5_IsD1Tuple_small_pair_excludes_three_in_disk

section
open scoped NumberField Classical
open Module

namespace D1Bound5



/-- In an ordered sextuple with exactly two small initial entries and a
nondegenerate anchor product, the fifth modulus exceeds 10^550. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 6 → 𝓞 K) (ht : IsD1Tuple t)
    (hmon : Monotone (fun i => ‖phi (t i : K)‖))
    (hsmall : ‖phi (t 1 : K)‖ < 3)
    (hlarge : 3 ≤ ‖phi (t 2 : K)‖)
    (hnondeg : t 0*t 1+1 ≠ 0) :
    (10 : ℝ)^550 < ‖phi (t 4 : K)‖ := by
  classical
  by_contra h
  have hle : ‖phi (t 4 : K)‖ ≤ (10 : ℝ)^550 := le_of_not_gt h
  let j : Fin 2 → Fin 6 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  let k : Fin 3 → Fin 6 := fun i => ⟨i.val+2, by omega⟩
  have hj : Function.Injective j := by
    intro i l hil
    apply Fin.ext
    exact congrArg (fun n : Fin 6 => n.val) hil
  have hk : Function.Injective k := by
    intro i l hil
    apply Fin.ext
    have heq := congrArg (fun n : Fin 6 => n.val) hil
    change i.val+2 = l.val+2 at heq
    omega
  have ha : IsD1Tuple (fun i => t (j i)) := by
    refine ⟨ht.1.comp hj, fun i => ht.2.1 (j i), ?_⟩
    intro i l hil
    exact ht.2.2 (j i) (j l) (fun h => hil (hj h))
  have hs : IsD1Tuple (fun i => t (k i)) := by
    refine ⟨ht.1.comp hk, fun i => ht.2.1 (k i), ?_⟩
    intro i l hil
    exact ht.2.2 (k i) (k l) (fun h => hil (hk h))
  refine IsD1Tuple.small_pair_excludes_three_in_disk hK phi
    (fun i => t (j i)) ha ?_ hnondeg (fun i => t (k i)) hs ?_ ?_ ?_
  · intro i
    have hi : j i ≤ (1 : Fin 6) := by change i.val ≤ 1; omega
    exact lt_of_le_of_lt (hmon hi) hsmall
  · intro i
    exact IsD1Tuple.properCommonExtension_first_two t ht (k i)
      (by change 2 ≤ i.val+2; omega)
  · intro i
    have hi : (2 : Fin 6) ≤ k i := by change 2 ≤ i.val+2; omega
    exact hlarge.trans (hmon hi)
  · intro i
    have hi : k i ≤ (4 : Fin 6) := by change i.val+2 ≤ 4; omega
    exact (hmon hi).trans hle

end D1Bound5
end
