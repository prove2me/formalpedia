-- Prove2me | solution 1 for D1Bound5.exists_frontier_fifteen_root_matrix
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:52.894831+00:00
-- url     : https://prove2.me/submissions/00e3c30e-9247-4fc1-b468-e1504b860e37

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FrontierFifteenRootError_Definitions
import Theorems.Thm_D1Bound5_exists_integral_root_rational_envelope

section
namespace D1Bound5









/-- The six manuscript near-half constants are realized simultaneously
by one symmetric integral root matrix. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ) (a : Fin 4 → R) (u : Fin 4 → ℂ)
    (hu : ∀ i, (u i)^2 = f (a i))
    (hr : ∀ i j, i ≠ j → ∃ r : R, r^2 = a i*a j+1)
    (hlarge : ∀ i j, i ≠ j → frontierFifteenMin i j ≤ ‖f (a i)*f (a j)‖) :
    ∃ S : Matrix (Fin 4) (Fin 4) R,
      (∀ i, S i i = a i) ∧ (∀ i j, S i j = S j i) ∧
      (∀ i j, i ≠ j → (S i j)^2 = a i*a j+1) ∧
      (∀ i j, i ≠ j →
        ‖u i*f (S i j)*u j-f (a i)*f (a j)-(1/2 : ℂ)‖ ≤ frontierFifteenK i j-1/2) := by
  obtain ⟨r01,hr01⟩ := hr 0 1 (by decide)
  obtain ⟨r02,hr02⟩ := hr 0 2 (by decide)
  obtain ⟨r03,hr03⟩ := hr 0 3 (by decide)
  obtain ⟨r12,hr12⟩ := hr 1 2 (by decide)
  obtain ⟨r13,hr13⟩ := hr 1 3 (by decide)
  obtain ⟨r23,hr23⟩ := hr 2 3 (by decide)
  obtain ⟨q01,hq01,he01⟩ := exists_integral_root_rational_envelope f (a 0) (a 1) r01
    (u 0) (u 1) (hu 0) (hu 1) hr01 3 (40/49) (5506/10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa [frontierFifteenMin] using hlarge 0 1 (by decide))
  obtain ⟨q02,hq02,he02⟩ := exists_integral_root_rational_envelope f (a 0) (a 2) r02
    (u 0) (u 2) (hu 0) (hu 2) hr02 15 (24/25) (5087/10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa [frontierFifteenMin] using hlarge 0 2 (by decide))
  obtain ⟨q03,hq03,he03⟩ := exists_integral_root_rational_envelope f (a 0) (a 3) r03
    (u 0) (u 3) (hu 0) (hu 3) hr03 90 (993/1000) (5014/10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa [frontierFifteenMin] using hlarge 0 3 (by decide))
  obtain ⟨q12,hq12,he12⟩ := exists_integral_root_rational_envelope f (a 1) (a 2) r12
    (u 1) (u 2) (hu 1) (hu 2) hr12 45 (49/50) (5029/10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa [frontierFifteenMin] using hlarge 1 2 (by decide))
  obtain ⟨q13,hq13,he13⟩ := exists_integral_root_rational_envelope f (a 1) (a 3) r13
    (u 1) (u 3) (hu 1) (hu 3) hr13 270 (99/100) (5005/10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa [frontierFifteenMin] using hlarge 1 3 (by decide))
  obtain ⟨q23,hq23,he23⟩ := exists_integral_root_rational_envelope f (a 2) (a 3) r23
    (u 2) (u 3) (hu 2) (hu 3) hr23 1350 (99/100) (5001/10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa [frontierFifteenMin] using hlarge 2 3 (by decide))
  have hq10 : q01^2 = a 1*a 0+1 := by
    calc
      q01^2 = a 0*a 1+1 := hq01
      _ = a 1*a 0+1 := by ring
  have he10 :
      ‖u 1*f q01*u 0-f (a 1)*f (a 0)-(1/2 : ℂ)‖ ≤ 5506/10000-1/2 := by
    calc
      _ = ‖u 0*f q01*u 1-f (a 0)*f (a 1)-(1/2 : ℂ)‖ := by
        congr 1
        ring
      _ ≤ _ := he01
  let S : Matrix (Fin 4) (Fin 4) R :=
    !![a 0,q01,q02,q03; q01,a 1,q12,q13; q02,q12,a 2,q23; q03,q13,q23,a 3]
  refine ⟨S,?_,?_,?_,?_⟩
  · intro i; fin_cases i <;> simp [S]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [S]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> try contradiction
    all_goals first
      | exact hq01
      | exact hq10
      | simpa [S,mul_comm] using hq01
      | simpa [S,mul_comm] using hq02
      | simpa [S,mul_comm] using hq03
      | simpa [S,mul_comm] using hq12
      | simpa [S,mul_comm] using hq13
      | simpa [S,mul_comm] using hq23
  · intro i j hij
    fin_cases i <;> fin_cases j <;> try contradiction
    all_goals first
      | exact he01
      | exact he10
      | simpa [S,frontierFifteenK,mul_comm,mul_left_comm,mul_assoc] using he01
      | simpa [S,frontierFifteenK,mul_comm,mul_left_comm,mul_assoc] using he02
      | simpa [S,frontierFifteenK,mul_comm,mul_left_comm,mul_assoc] using he03
      | simpa [S,frontierFifteenK,mul_comm,mul_left_comm,mul_assoc] using he12
      | simpa [S,frontierFifteenK,mul_comm,mul_left_comm,mul_assoc] using he13
      | simpa [S,frontierFifteenK,mul_comm,mul_left_comm,mul_assoc] using he23

end D1Bound5
end
