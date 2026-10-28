-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.all_large_impossible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T22:50:50.546306+00:00
-- url     : https://prove2.me/submissions/d3424531-504f-4442-804a-d9ad7fae7788

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_AllLargeWindows_Definitions
import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_IsD1Tuple
import Theorems.Thm_D1Bound5_IsD1Tuple_all_large_forced_P_window
import Theorems.Thm_D1Bound5_IsD1Tuple_all_large_retained_growth
import Theorems.Thm_D1Bound5_IsD1Tuple_all_large_retained_start
import Theorems.Thm_D1Bound5_full_ring_finiteP_closed_interval_excluded

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5

/-- No ordered sextuple of nonzero full-ring integers has all moduli
at least three. Every approximation family, including P, is obtained
from its actual integral matrix; there are no interval or analytic
certificate hypotheses in this endpoint. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hA : 3 ≤ ‖phi (a 0 : K)‖) : False := by
  classical
  let A := ‖phi (a 0 : K)‖
  let B := ‖phi (a 1 : K)‖
  let S := ‖phi (a 2 : K)‖
  let T := ‖phi (a 3 : K)‖
  let C := ‖phi (a 4 : K)‖
  let D := ‖phi (a 5 : K)‖
  have hAB : A ≤ B := hmon (by decide : (0 : Fin 6) ≤ 1)
  have hBS : B ≤ S := hmon (by decide : (1 : Fin 6) ≤ 2)
  have hB : 3 ≤ B := hA.trans hAB
  have hS : 3 ≤ S := hB.trans hBS
  have hA1 : 1 ≤ A := by linarith only [hA]
  have hB1 : 1 ≤ B := by linarith only [hB]
  have hS1 : 1 ≤ S := by linarith only [hS]
  have hret := ha.all_large_retained_start hK phi a hmon hA
  change A^2*T^5/S^2 < C ∧ A^2*C^5/S^2 < D ∧ A^2*C^7/(S^2*T^4) < D ∧
    1000 < C ∧ 16*B*S*T < C ∧ 1000*C < D at hret
  have hC0 : 0 < C := by linarith only [hret.2.2.2.1]
  let i5 : Fin 5 → Fin 6 := ![0,1,2,3,4]
  have hi5 : Function.Injective i5 := by decide
  have hb5 : IsD1Tuple (fun i => a (i5 i)) := by
    refine ⟨ha.1.comp hi5,fun i => ha.2.1 (i5 i),?_⟩
    exact fun i j hij => ha.2.2 (i5 i) (i5 j) (hi5.ne hij)
  have hm5 : Monotone i5 := by decide
  have hgap : 400*(A^7*B^5*S^3) < C :=
    hb5.all_large_retained_growth hK phi (fun i => a (i5 i)) (hmon.comp hm5) hA
  have hC200S : 200*S ≤ C := by
    have hh : 400*S ≤ 400*(A^7*B^5*S^3) := by
      calc
        400*S = 400*((1 : ℝ)^7*1^5*S*1^2) := by ring
        _ ≤ 400*(A^7*B^5*S*S^2) := by gcongr
        _ = 400*(A^7*B^5*S^3) := by ring
    linarith only [hh,hgap,hS]
  have hAC : 1000 ≤ A*C := by
    have hh := mul_le_mul_of_nonneg_right hA1 hC0.le
    linarith only [hh,hret.2.2.2.1]
  let Tup : Finset (𝓞 K) := Finset.univ.image a
  have hmem (i : Fin 6) : a i ∈ Tup := Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  have hTup : IsD1 Tup := by
    constructor
    · intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact ha.2.1 i
    · intro x hx y hy hxy
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
      exact ha.2.2 i j (fun hij => hxy (congrArg a hij))
  let i3 : Fin 3 → Fin 6 := ![0,1,2]
  let b : Fin 3 → 𝓞 K := fun i => a (i3 i)
  have hi3 : Function.Injective i3 := by decide
  have hm3 : Monotone i3 := by decide
  have hw := ha.all_large_forced_P_window hK phi a hmon hA
  exact full_ring_finiteP_closed_interval_excluded hK phi hTup b (a 4) (a 5)
    (fun j => hmem (i3 j)) (hmem 4) (hmem 5) (ha.1.comp hi3)
    (fun j => ha.1.ne (by fin_cases j <;> decide))
    (fun j => ha.1.ne (by fin_cases j <;> decide))
    (ha.1.ne (by decide : (4 : Fin 6) ≠ 5)) (hmon.comp hm3)
    hC200S (hmon (by decide : (4 : Fin 6) ≤ 5)) hAC hw.1 hw.2

end D1Bound5
end
