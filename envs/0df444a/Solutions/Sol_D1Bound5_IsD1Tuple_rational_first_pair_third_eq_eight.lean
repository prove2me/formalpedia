-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.rational_first_pair_third_eq_eight
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:15:26.605832+00:00
-- url     : https://prove2.me/submissions/aadccf96-bad0-4d92-b8bb-df33f233340c

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
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
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
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
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_001
import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_rational_first_pair_third_lt_fifteen
import Theorems.Thm_D1Bound5_IsD1_one_three_small_third_eq_eight
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_rationalCutoff_pair_geometry

section
open scoped NumberField
open Module

namespace D1Bound5

/-- Every ordered actual sextuple beginning with the signed rational
pair has the same signed8 as its third entry. The fixed field is unchanged. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (sgn : Bool) (hx : a 0 = if sgn then -1 else 1)
    (hy : a 1 = if sgn then -3 else 3) :
    a 2 = if sgn then -8 else 8 := by
  classical
  have hS15 := IsD1Tuple.rational_first_pair_third_lt_fifteen hK phi a ha hmon sgn hx hy
  obtain ⟨_,hB,_⟩ := rationalCutoff_pair_geometry phi sgn (a 0) (a 1) hx hy
  let u : Fin 6 → 𝓞 K := fun i => if sgn then -a i else a i
  have hu : IsD1Tuple u := by
    cases sgn
    · exact ha
    · refine ⟨?_,?_,?_⟩
      · intro i j hij
        exact ha.1 (neg_injective hij)
      · intro i hi
        exact ha.2.1 i (neg_eq_zero.mp hi)
      · intro i j hij
        obtain ⟨r,hr⟩ := ha.2.2 i j hij
        exact ⟨r,by simpa [u] using hr⟩
  have hu0 : u 0=1 := by cases sgn <;> simp [u,hx]
  have hu1 : u 1=3 := by cases sgn <;> simp [u,hy]
  have hnorm (i : Fin 6) : ‖phi (u i : K)‖ = ‖phi (a i : K)‖ := by
    cases sgn <;> simp [u]
  let S : Finset (𝓞 K) := Finset.univ.image u
  have hmem (i : Fin 6) : u i ∈ S := Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  have hSet : IsD1 S := by
    constructor
    · intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact hu.2.1 i
    · intro x hx y hy hxy
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
      exact hu.2.2 i j (fun hij => hxy (congrArg u hij))
  have hcard : S.card=6 := by
    change (Finset.univ.image u).card = 6
    rw [Finset.card_image_of_injective Finset.univ hu.1]
    simp
  have hS3 : 3 ≤ ‖phi (a 2 : K)‖ := by
    rw [←hB]
    exact hmon (by decide : (1 : Fin 6) ≤ 2)
  have hu2 : u 2=8 := hSet.one_three_small_third_eq_eight hK phi
    (by simpa only [hu0] using hmem 0) (by simpa only [hu1] using hmem 1)
    (by omega) (u 2) (hmem 2)
    (by rw [←hu0]; exact hu.1.ne (by decide))
    (by rw [←hu1]; exact hu.1.ne (by decide))
    (by rw [hnorm]; nlinarith only [hS3])
    (by rw [hnorm]; nlinarith only [hS15,norm_nonneg (phi (a 2 : K))])
  cases sgn <;> simpa [u,neg_eq_iff_eq_neg] using hu2

end D1Bound5
end
