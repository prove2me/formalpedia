-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.fixed_cutoff_forced_P_window
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:47:09.922277+00:00
-- url     : https://prove2.me/submissions/543cab8e-23ac-43b5-97d3-12766dd4df6d

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
import Definitions.Def_D1Bound5_AllLargeWindows_Definitions
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallFixedWindows_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_OrdinaryClosedIntervals_Definitions
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_fixed_cutoff_above_Q
import Theorems.Thm_D1Bound5_IsD1Tuple_fixed_cutoff_retained_gap
import Theorems.Thm_D1Bound5_IsD1Tuple_ordinary_closed_interval_excluded
import Theorems.Thm_D1Bound5_IsD1Tuple_ordinary_tail_incompatible
import Theorems.Thm_D1Bound5_fixed_cutoff_window_overlaps
import Theorems.Thm_D1Bound5_full_ring_finiteA3_fixed_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteA4_fixed_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteA5_fixed_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteM_closed_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteN2_fixed_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteN3Ab_fixed_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteN3Bs_fixed_interval_excluded
import Theorems.Thm_D1Bound5_norm_sq_full_ring_equiv
import Theorems.Thm_D1Bound5_oneSmall_fixed_pair_geometry
import Theorems.Thm_D1Bound5_one_le_norm_integer
import Theorems.Thm_D1Bound5_smallExtensionSymmetry_norm
import Theorems.Thm_D1Bound5_window_upper_lt_of_excluded

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- An actual normalized fixed triple beyond its printed cutoff forces
its actual adaptive P window. Every other finite window, the retained
start, all adjacent overlaps, and the infinite ordinary tail are proved
from the tuple; no exclusion or approximation estimate is assumed. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (r : OneSmallCutoffRow) (hr : r ∈ oneSmallCutoffRows)
    (e : QuadInt r.triple.tau r.triple.nu ≃+* 𝓞 K)
    (sgn conj : Bool)
    (h0 : smallExtensionSymmetry sgn conj (e.symm (a 0)) = r.triple.anchorA)
    (h1 : smallExtensionSymmetry sgn conj (e.symm (a 1)) = r.triple.anchorB)
    (h2 : smallExtensionSymmetry sgn conj (e.symm (a 2)) = r.triple.anchorS)
    (hlarge : (r.triple.cutoff : ℝ) ≤ ‖phi (a 3 : K)‖^2) :
    let B := ‖phi (a 1 : K)‖
    let S := ‖phi (a 2 : K)‖
    let C := ‖phi (a 4 : K)‖
    let D := ‖phi (a 5 : K)‖
    (fixedWindowP r B S C).1 ≤ D ∧ D ≤ (fixedWindowP r B S C).2 := by
  classical
  let A := ‖phi (a 0 : K)‖
  let B := ‖phi (a 1 : K)‖
  let S := ‖phi (a 2 : K)‖
  let T := ‖phi (a 3 : K)‖
  let C := ‖phi (a 4 : K)‖
  let D := ‖phi (a 5 : K)‖
  change (fixedWindowP r B S C).1 ≤ D ∧ D ≤ (fixedWindowP r B S C).2
  have hAB : A ≤ B := hmon (by decide : (0 : Fin 6) ≤ 1)
  have hBS : B ≤ S := hmon (by decide : (1 : Fin 6) ≤ 2)
  have hST : S ≤ T := hmon (by decide : (2 : Fin 6) ≤ 3)
  have hCD : C ≤ D := hmon (by decide : (4 : Fin 6) ≤ 5)
  have hA1 : 1 ≤ A := one_le_norm_integer hK phi (ha.2.1 0)
  have hA : 0 < A := by linarith only [hA1]
  have hB : 0 < B := hA.trans_le hAB
  have hS : 0 < S := hB.trans_le hBS
  have hT : 0 < T := hS.trans_le hST
  have hret := IsD1Tuple.fixed_cutoff_retained_gap hK phi a ha hmon r hr e sgn conj h0 h1 h2 hlarge
  change (r.retainedCoefficient : ℝ)*T^5/S^2 < C ∧
    A^2*C^5/S^2 < D ∧ A^2*C^7/(S^2*T^4) < D ∧
    1000 < C ∧ 200*S < C ∧ 4*T < C ∧ 16*B*S*T < C ∧ 1000*C < D at hret
  obtain ⟨hgap,_,_,hC1000,hC200S,hC4T,_,_⟩ := hret
  have hC : 0 < C := by linarith only [hC1000]
  have hC200B : 200*B ≤ C := (by gcongr : 200*B ≤ 200*S).trans hC200S.le
  have hC4S : 4*S ≤ C := (by gcongr : 4*S ≤ 4*T).trans hC4T.le
  have hC4B : 4*B < C := by linarith only [hC200B,hB]
  have hAC : 1000 ≤ A*C := by
    have hh := mul_le_mul_of_nonneg_right hA1 hC.le
    linarith only [hh,hC1000]
  obtain ⟨_,hBsq,_,_⟩ := oneSmall_fixed_pair_geometry phi r hr e sgn conj (a 0) (a 1) h0 h1
  have hSsq : S^2 = (r.s0 : ℝ) := by
    have hn : ‖phi (a 2 : K)‖^2 =
        ((smallExtensionSymmetry sgn conj (e.symm (a 2))).norm : ℝ) := by
      simpa only [smallExtensionSymmetry_norm,RingEquiv.apply_symm_apply] using
        norm_sq_full_ring_equiv e phi (e.symm (a 2))
    rw [h2] at hn
    simpa [OneSmallCutoffRow.s0] using hn
  obtain ⟨hoQN2,hoN2P,hoPA3,hoA3M,hoMN3,hoN3bs,hoBsA4,hoA4O4,hoO4A5,hoA5O5,hoO5O6,hoRate⟩ :=
    fixed_cutoff_window_overlaps r hr B S T C hB hS hT hBsq hSsq hlarge hgap
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
  have hN2 : ¬ ((fixedWindowN2 r B C).1 ≤ D ∧ D ≤ (fixedWindowN2 r B C).2) := by
    rintro ⟨hl,hu⟩
    exact full_ring_finiteN2_fixed_interval_excluded hK phi hTup (a 0) (a 1) (a 4) (a 5)
      (hmem 0) (hmem 1) (hmem 4) (hmem 5)
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      hAB hC1000.le hC200B hCD r hr e sgn conj h0 h1 hl hu
  have hN3 : ¬ ((fixedWindowN3 r B C).1 ≤ D ∧ D ≤ (fixedWindowN3 r B C).2) := by
    rintro ⟨hl,hu⟩
    exact full_ring_finiteN3Ab_fixed_interval_excluded hK phi hTup (a 0) (a 1) (a 4) (a 5)
      (hmem 0) (hmem 1) (hmem 4) (hmem 5)
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      hAB hC1000.le hC200B hCD r hr e sgn conj h0 h1 hl hu
  have hN3bs : ¬ ((fixedWindowN3bs r B S C).1 ≤ D ∧ D ≤ (fixedWindowN3bs r B S C).2) := by
    rintro ⟨hl,hu⟩
    exact full_ring_finiteN3Bs_fixed_interval_excluded hK phi hTup (a 1) (a 2) (a 4) (a 5)
      (hmem 1) (hmem 2) (hmem 4) (hmem 5)
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      hBS hC1000.le hC200S.le hCD r hr e sgn conj h1 h2 hl hu
  have hA3 : ¬ ((fixedWindowA3 r B C).1 ≤ D ∧ D ≤ (fixedWindowA3 r B C).2) := by
    rintro ⟨hl,hu⟩
    exact full_ring_finiteA3_fixed_interval_excluded hK phi hTup (a 0) (a 1) (a 4) (a 5)
      (hmem 0) (hmem 1) (hmem 4) (hmem 5)
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      hAB hC1000.le hC200B hCD r hr e sgn conj h0 h1 hl hu
  have hA4 : ¬ ((fixedWindowA4 r B C).1 ≤ D ∧ D ≤ (fixedWindowA4 r B C).2) := by
    rintro ⟨hl,hu⟩
    exact full_ring_finiteA4_fixed_interval_excluded hK phi hTup (a 0) (a 1) (a 4) (a 5)
      (hmem 0) (hmem 1) (hmem 4) (hmem 5)
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      hAB hC1000.le hC200B hCD r hr e sgn conj h0 h1 hl hu
  have hA5 : ¬ ((fixedWindowA5 r B C).1 ≤ D ∧ D ≤ (fixedWindowA5 r B C).2) := by
    rintro ⟨hl,hu⟩
    exact full_ring_finiteA5_fixed_interval_excluded hK phi hTup (a 0) (a 1) (a 4) (a 5)
      (hmem 0) (hmem 1) (hmem 4) (hmem 5)
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      hAB hC1000.le hC200B hCD r hr e sgn conj h0 h1 hl hu
  let i3 : Fin 3 → Fin 6 := ![0,1,2]
  let b3 : Fin 3 → 𝓞 K := fun i => a (i3 i)
  have hi3 : Function.Injective i3 := by decide
  have hb3 : Function.Injective b3 := ha.1.comp hi3
  have hm3 : Monotone i3 := by decide
  have hM : ¬ ((allLargeWindowM 1 B S C).1 ≤ D ∧ D ≤ (allLargeWindowM 1 B S C).2) := by
    rintro ⟨hl,hu⟩
    have hu' : D ≤ A^6*C^11/(4*(3920/81 : ℝ)^2*B^4*S^10*(1+1/4000 : ℝ)) := by
      apply hu.trans
      simp only [allLargeWindowM,one_pow,one_mul]
      gcongr
      have hA6 : (1 : ℝ) ≤ A^6 := one_le_pow₀ hA1
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hA6 (pow_nonneg hC.le 11)
    exact full_ring_finiteM_closed_interval_excluded hK phi hTup b3 (a 4) (a 5)
      (fun j => hmem (i3 j)) (hmem 4) (hmem 5) hb3
      (fun j => ha.1.ne (by fin_cases j <;> decide))
      (fun j => ha.1.ne (by fin_cases j <;> decide))
      (ha.1.ne (by decide : (4 : Fin 6) ≠ 5)) (hmon.comp hm3) hC4S hCD hAC hl hu'
  let iAB : Fin 4 → Fin 6 := ![0,1,4,5]
  let tAB : Fin 4 → 𝓞 K := fun i => a (iAB i)
  have hiAB : Function.Injective iAB := by decide
  have htAB : IsD1Tuple tAB :=
    ⟨ha.1.comp hiAB,fun j => ha.2.1 _,fun j k hjk => ha.2.2 _ _ (hiAB.ne hjk)⟩
  have hOU (k : ℕ) : ordinaryWindowUpper 1 B C k ≤ ordinaryWindowUpper A B C k := by
    unfold ordinaryWindowUpper
    gcongr
  have hQupper : (allLargeWindowQ 1 T C).2 < D := by
    have hh := IsD1Tuple.fixed_cutoff_above_Q hK phi a ha hmon r hr e sgn conj h0 h1 h2 hlarge
    simpa only [allLargeWindowQ,one_pow,one_mul] using hh
  have hN2upper := window_upper_lt_of_excluded _ D hN2 (hoQN2.trans hQupper).le
  have hPlower : (fixedWindowP r B S C).1 ≤ D := (hoN2P.trans hN2upper).le
  refine ⟨hPlower,?_⟩
  by_contra hn
  have hPupper : (fixedWindowP r B S C).2 < D := lt_of_not_ge hn
  have hA3upper := window_upper_lt_of_excluded _ D hA3 (hoPA3.trans hPupper).le
  have hMupper := window_upper_lt_of_excluded _ D hM (hoA3M.trans hA3upper).le
  have hN3upper := window_upper_lt_of_excluded _ D hN3 (hoMN3.trans hMupper).le
  have hN3bsupper := window_upper_lt_of_excluded _ D hN3bs (hoN3bs.trans hN3upper).le
  have hA4upper := window_upper_lt_of_excluded _ D hA4 (hoBsA4.trans hN3bsupper).le
  have hO4lower : ordinaryWindowLower B C 4 ≤ D := (hoA4O4.trans hA4upper).le
  have hO4upper : ordinaryWindowUpper 1 B C 4 < D := by
    apply lt_of_not_ge
    intro h
    exact IsD1Tuple.ordinary_closed_interval_excluded hK phi tAB htAB hAB hAC hC4B hCD
      4 (by norm_num) hO4lower (h.trans (hOU 4))
  have hA5upper := window_upper_lt_of_excluded _ D hA5 (hoO4A5.trans hO4upper).le
  have hO5lower : ordinaryWindowLower B C 5 ≤ D := (hoA5O5.trans hA5upper).le
  have hrate : 42*B^3*C < 2*A*C^2/(5*B) := by
    apply hoRate.trans_le
    gcongr
    linarith only [hA1]
  exact IsD1Tuple.ordinary_tail_incompatible hK phi tAB htAB hAB hAC hC4B hCD
    hrate (hoO5O6.le.trans (hOU 5)) hO5lower

end D1Bound5
end
