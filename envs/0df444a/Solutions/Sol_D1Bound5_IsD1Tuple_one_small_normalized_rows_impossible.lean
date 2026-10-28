-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.one_small_normalized_rows_impossible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:21:58.489861+00:00
-- url     : https://prove2.me/submissions/139e3a00-0b92-4605-97fb-1f6257abf9c6

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
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_OneSmallSymmetry_Definitions
import Definitions.Def_D1Bound5_Regular_Definitions
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_fixed_cutoff_fourth_norm_sq_lt
import Theorems.Thm_D1Bound5_IsD1Tuple_tail_irregular_and_growth
import Theorems.Thm_D1Bound5_IsD1_card_le_four_of_one_three_negative
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_norm_sq_full_ring_equiv
import Theorems.Thm_D1Bound5_oneSmallFixedRows_cutoff_member
import Theorems.Thm_D1Bound5_oneSmallFixedRows_metadata
import Theorems.Thm_D1Bound5_oneSmallRowMembership_full_ring_excludes_irregular_bound
import Theorems.Thm_D1Bound5_smallExtensionSymmetry_norm

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

private theorem normalized_integer_anchor
    {K : Type*} [Field K] [NumberField K]
    {tau nu : ℤ} (e : QuadInt tau nu ≃+* 𝓞 K) (sgn conj : Bool)
    (z : 𝓞 K) (n : ℤ)
    (h : smallExtensionSymmetry sgn conj (e.symm z) = (n : QuadInt tau nu)) :
    (if sgn then -z else z) = (n : 𝓞 K) := by
  have hc : (if sgn then -e.symm z else e.symm z) = (n : QuadInt tau nu) := by
    cases sgn <;> cases conj
    · simpa [smallExtensionSymmetry] using h
    · simpa [smallExtensionSymmetry] using congrArg star h
    · simpa [smallExtensionSymmetry] using h
    · simpa [smallExtensionSymmetry] using congrArg star h
  cases sgn <;>
    simpa only [Bool.false_eq_true,if_false,if_true,map_neg,map_intCast,
      RingEquiv.apply_symm_apply] using congrArg e hc

private theorem normalized_one_neg_three_three_impossible
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    {tau nu : ℤ} (e : QuadInt tau nu ≃+* 𝓞 K) (sgn conj : Bool)
    (h0 : smallExtensionSymmetry sgn conj (e.symm (a 0)) = 1)
    (h1 : smallExtensionSymmetry sgn conj (e.symm (a 1)) = -3)
    (h2 : smallExtensionSymmetry sgn conj (e.symm (a 2)) = 3) : False := by
  classical
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
        refine ⟨r,?_⟩
        change r*r = (-a i)*(-a j)+1
        simpa only [neg_mul_neg] using hr
  have hu0 : u 0=1 := by
    simpa only [u,Int.cast_one,Int.cast_neg,Int.cast_ofNat] using
      normalized_integer_anchor e sgn conj (a 0) 1 (by simpa using h0)
  have hu1 : u 1=-3 := by
    simpa only [u,Int.cast_one,Int.cast_neg,Int.cast_ofNat] using
      normalized_integer_anchor e sgn conj (a 1) (-3) (by simpa using h1)
  have hu2 : u 2=3 := by
    simpa only [u,Int.cast_one,Int.cast_neg,Int.cast_ofNat] using
      normalized_integer_anchor e sgn conj (a 2) 3 (by simpa using h2)
  let S : Finset (𝓞 K) := Finset.univ.image u
  have hmem (i : Fin 6) : u i ∈ S := Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  have hS : IsD1 S := by
    constructor
    · intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact hu.2.1 i
    · intro x hx y hy hxy
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
      exact hu.2.2 i j (fun hij => hxy (congrArg u hij))
  have hcard : S.card=6 := by
    dsimp only [S]
    rw [Finset.card_image_of_injective Finset.univ hu.1]
    simp
  have hbound := hS.card_le_four_of_one_three_negative hK
    (by simpa only [hu0] using hmem 0) (by simpa only [hu2] using hmem 2)
    ⟨-3,by norm_num,by simpa [hu1] using hmem 1⟩
  omega

/-- Complete analytic/finite join for any of the56 normalized nonrational
first-triple rows. It uses the actual fourth-entry cutoff and the exact
finite extension theorem, against the actual tail-growth lower bound. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    {tau nu : ℤ} (e : QuadInt tau nu ≃+* 𝓞 K)
    (hrows : OneSmallNormalizedThirdRows (e.symm (a 0)) (e.symm (a 1)) (e.symm (a 2))) :
    False := by
  classical
  obtain ⟨sgn,conj,hrows⟩ := hrows
  dsimp only at hrows
  rcases hrows with ⟨h0,h1,h2⟩ | ⟨cutoff,hrow⟩
  · exact normalized_one_neg_three_three_impossible hK a ha e sgn conj h0 h1 h2
  · let F : 𝓞 K → QuadInt tau nu := fun z => smallExtensionSymmetry sgn conj (e.symm z)
    let r : OneSmallTripleRow :=
      ⟨tau,nu,((F (a 0)).re,(F (a 0)).im),((F (a 1)).re,(F (a 1)).im),
        ((F (a 2)).re,(F (a 2)).im),cutoff⟩
    have hr : r ∈ oneSmallFixedRows := hrow
    obtain ⟨c0,hc0,hc0r⟩ := oneSmallFixedRows_cutoff_member r hr
    let c : OneSmallCutoffRow := {c0 with triple := r}
    have hceq : c=c0 := by
      exact (congrArg (fun t : OneSmallTripleRow => {c0 with triple := t}) hc0r).symm
    have hc : c ∈ oneSmallCutoffRows := by rw [hceq]; exact hc0
    have h0 : F (a 0) = c.triple.anchorA := by apply QuadraticAlgebra.ext <;> rfl
    have h1 : F (a 1) = c.triple.anchorB := by apply QuadraticAlgebra.ext <;> rfl
    have h2 : F (a 2) = c.triple.anchorS := by apply QuadraticAlgebra.ext <;> rfl
    have hcut := ha.fixed_cutoff_fourth_norm_sq_lt hK phi a hmon c hc e sgn conj h0 h1 h2
    change ‖phi (a 3 : K)‖^2 < (cutoff : ℝ) at hcut
    obtain ⟨_,_,hBN,_⟩ := oneSmallFixedRows_metadata r hr
    have hnorm : ‖phi (a 1 : K)‖^2 = ((F (a 1)).norm : ℝ) := by
      simpa only [F,smallExtensionSymmetry_norm,RingEquiv.apply_symm_apply] using
        norm_sq_full_ring_equiv e phi (e.symm (a 1))
    have hBsq : (9 : ℝ) ≤ ‖phi (a 1 : K)‖^2 := by
      rw [hnorm]
      exact_mod_cast hBN
    have hB : 3 ≤ ‖phi (a 1 : K)‖ :=
      (sq_le_sq₀ (by norm_num) (norm_nonneg _)).mp
        (by simpa only [show (3 : ℝ)^2 = 9 by norm_num] using hBsq)
    let ii : Fin 4 → Fin 6 := ![0,1,2,3]
    have hi : Function.Injective ii := by decide
    have him : Monotone ii := by decide
    let t : Fin 4 → 𝓞 K := fun i => a (ii i)
    have ht : IsD1Tuple t := by
      refine ⟨ha.1.comp hi,fun i => ha.2.1 (ii i),?_⟩
      intro i j hij
      exact ha.2.2 (ii i) (ii j) (fun h => hij (hi h))
    have hg : 2*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖ < ‖phi (a 3 : K)‖ :=
      (ht.tail_irregular_and_growth hK phi t (hmon.comp him) hB).2
    have hg2 : 4*‖phi (a 1 : K)‖^2*‖phi (a 2 : K)‖^2 < ‖phi (a 3 : K)‖^2 := by
      have hh := (sq_lt_sq₀ (by positivity : 0 ≤ 2*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖)
        (norm_nonneg (phi (a 3 : K)))).mpr hg
      nlinarith only [hh]
    exact oneSmallRowMembership_full_ring_excludes_irregular_bound e phi sgn conj
      (a 0) (a 1) (a 2) (a 3) cutoff hrow hcut
      (ha.2.2 0 3 (by decide)) (ha.2.2 1 3 (by decide)) (ha.2.2 2 3 (by decide)) hg2

end D1Bound5
end
