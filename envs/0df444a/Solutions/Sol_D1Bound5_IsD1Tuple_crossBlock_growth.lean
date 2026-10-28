-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.crossBlock_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:49:22.307684+00:00
-- url     : https://prove2.me/submissions/1313173e-d187-4d62-9d6e-f000304f506d

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_IsD1Tuple
import Theorems.Thm_D1Bound5_full_ring_crossBlock_growth

section
open scoped BigOperators NumberField
open Module

namespace D1Bound5









/-- The manuscript's cross-block inequality for any two disjoint triples
inside an actual D(1)-tuple. Only the stated separate order and initial
size hypotheses remain. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {n : ℕ} (t : Fin n → 𝓞 K) (ht : IsD1Tuple t)
    (p q : Fin 3 ↪ Fin n) (hpq : ∀ i j, p i ≠ q j)
    (hmonA : Monotone (fun i => ‖phi (t (p i) : K)‖))
    (hmonB : Monotone (fun i => ‖phi (t (q i) : K)‖))
    (hlarge : 9 ≤ ‖phi (t (p 0) : K)‖*‖phi (t (q 0) : K)‖) :
    (‖phi (t (p 0) : K)‖*‖phi (t (q 0) : K)‖)^3*
        (‖phi (t (p 1) : K)‖*‖phi (t (q 1) : K)‖)/7 <
      ‖phi (t (p 2) : K)‖*‖phi (t (q 2) : K)‖ := by
  classical
  have hex (i j : Fin 3) : ∃ r : 𝓞 K, r^2 = t (p i)*t (q j)+1 := by
    simpa only [pow_two] using ht.2.2 (p i) (q j) (hpq i j)
  choose M hM using hex
  exact full_ring_crossBlock_growth hK phi (fun i => t (p i)) (fun j => t (q j))
    M (ht.1.comp p.injective) (ht.1.comp q.injective) hM hmonA hmonB hlarge

end D1Bound5
end
