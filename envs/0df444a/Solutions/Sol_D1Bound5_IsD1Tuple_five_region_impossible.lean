-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.five_region_impossible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:30:30.769003+00:00
-- url     : https://prove2.me/submissions/94891c53-21ce-47a0-b3f7-2cf1d1f52374

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
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
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
import Definitions.Def_D1Bound5_CommonIntervalWindows_Definitions
import Definitions.Def_D1Bound5_CoupledPhaseGeometry_Definitions
import Definitions.Def_D1Bound5_FiniteA3RatioHeight_Definitions
import Definitions.Def_D1Bound5_FiniteA4RatioHeight_Definitions
import Definitions.Def_D1Bound5_FiniteA5RatioHeight_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions
import Definitions.Def_D1Bound5_FiniteN2RatioHeight_Definitions
import Definitions.Def_D1Bound5_FiniteN3RatioHeight_Definitions
import Definitions.Def_D1Bound5_FiveRegionParameters_Definitions
import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OrdinaryClosedIntervals_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_five_region_retained_gaps
import Theorems.Thm_D1Bound5_IsD1Tuple_ordinary_closed_interval_excluded
import Theorems.Thm_D1Bound5_IsD1Tuple_ordinary_tail_incompatible
import Theorems.Thm_D1Bound5_IsD1Tuple_small_norm_retained_parameters
import Theorems.Thm_D1Bound5_IsD1Tuple_small_norm_retained_start
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_common_interval_window_overlaps
import Theorems.Thm_D1Bound5_fiveRegion_case_bounds
import Theorems.Thm_D1Bound5_fiveRegion_case_disjunction
import Theorems.Thm_D1Bound5_fiveRegion_common_overlap_bounds
import Theorems.Thm_D1Bound5_full_ring_finiteA3_five_region_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteA4_five_region_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteA5_five_region_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteM_closed_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteN2_five_region_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteN3_five_region_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteN3_phi_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteP_five_region_interval_excluded
import Theorems.Thm_D1Bound5_full_ring_finiteQ_closed_interval_excluded
import Theorems.Thm_D1Bound5_one_le_norm_integer
import Theorems.Thm_D1Bound5_window_upper_lt_of_excluded

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5

private theorem fiveRegion_subtuple
    {R : Type*} [CommRing R] {m n : ℕ} (a : Fin n → R) (ha : IsD1Tuple a)
    (i : Fin m → Fin n) (hi : Function.Injective i) : IsD1Tuple (fun j => a (i j)) :=
  ⟨ha.1.comp hi, fun j => ha.2.1 (i j), fun j k hjk => ha.2.2 (i j) (i k) (hi.ne hjk)⟩

/-- Every unbounded first-pair region is impossible for an actual
ordered sextuple. All coefficient heights, residual rates, retained
gaps, phase bounds, finite windows, and the infinite tail are supplied
by their proved constructions; no interval certificate is assumed. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (r : Fin 5) (hN8 : ‖phi (a 0 : K)‖^2 ≤ 8)
    (hcase : FiveRegionCase r ‖phi (a 0 : K)‖ ‖phi (a 1 : K)‖) : False := by
  classical
  let A := ‖phi (a 0 : K)‖
  let B := ‖phi (a 1 : K)‖
  let S := ‖phi (a 2 : K)‖
  let T := ‖phi (a 3 : K)‖
  let C := ‖phi (a 4 : K)‖
  let D := ‖phi (a 5 : K)‖
  let i3 : Fin 3 → Fin 6 := ![0,1,2]
  let i4 : Fin 4 → Fin 6 := ![0,1,2,3]
  let i5 : Fin 5 → Fin 6 := ![0,1,2,3,4]
  let iAB : Fin 4 → Fin 6 := ![0,1,4,5]
  let iBS : Fin 4 → Fin 6 := ![1,2,4,5]
  let b3 : Fin 3 → 𝓞 K := fun i => a (i3 i)
  let b4 : Fin 4 → 𝓞 K := fun i => a (i4 i)
  let b5 : Fin 5 → 𝓞 K := fun i => a (i5 i)
  let tAB : Fin 4 → 𝓞 K := fun i => a (iAB i)
  let tBS : Fin 4 → 𝓞 K := fun i => a (iBS i)
  have hi3 : Function.Injective i3 := by decide
  have hi4 : Function.Injective i4 := by decide
  have hi5 : Function.Injective i5 := by decide
  have hiAB : Function.Injective iAB := by decide
  have hiBS : Function.Injective iBS := by decide
  have hb3 := fiveRegion_subtuple a ha i3 hi3
  have hb4 := fiveRegion_subtuple a ha i4 hi4
  have hb5 := fiveRegion_subtuple a ha i5 hi5
  have htAB := fiveRegion_subtuple a ha iAB hiAB
  have htBS := fiveRegion_subtuple a ha iBS hiBS
  have hm3 : Monotone i3 := by decide
  have hm4 : Monotone i4 := by decide
  have hm5 : Monotone i5 := by decide
  have hAB : A ≤ B := hmon (by decide : (0 : Fin 6) ≤ 1)
  have hBS : B ≤ S := hmon (by decide : (1 : Fin 6) ≤ 2)
  have hST : S ≤ T := hmon (by decide : (2 : Fin 6) ≤ 3)
  have hTC : T ≤ C := hmon (by decide : (3 : Fin 6) ≤ 4)
  have hCD : C ≤ D := hmon (by decide : (4 : Fin 6) ≤ 5)
  have hA1 : 1 ≤ A := one_le_norm_integer hK phi (ha.2.1 0)
  have hc := fiveRegion_case_bounds r A B (norm_nonneg _) hN8 hcase
  have hB : 3 ≤ B := hc.2.2.2.1
  have hS : 3 ≤ S := hB.trans hBS
  have hA0 : 0 < A := by linarith only [hA1]
  have hB0 : 0 < B := by linarith only [hB]
  have hS0 : 0 < S := by linarith only [hS]
  have hT0 : 0 < T := hS0.trans_le hST
  have hB1 : 1 ≤ B := by linarith only [hB]
  have hS1 : 1 ≤ S := by linarith only [hS]
  have hret := IsD1Tuple.small_norm_retained_start hK phi a ha hmon hN8 hB
    (fiveRegion_case_disjunction r A B hcase)
  change A^2*T^5/S^2 < C ∧ A^2*C^5/S^2 < D ∧ A^2*C^7/(S^2*T^4) < D ∧
    1000 < C ∧ 200*S < C ∧ 4*T < C ∧ 16*B*S*T < C ∧ 1000*C < D at hret
  rcases hret with ⟨hCgap,hDgap,hDstart,hC1000,hC200S',hC4T',hC16,hD1000⟩
  let Rbs : ℝ := (3535/409600)*phasePhi (phi (a 1 : K)) (phi (a 2 : K))
  have hgapBoth := IsD1Tuple.five_region_retained_gaps hK phi b5 hb5 (hmon.comp hm5) r hN8 hcase
  have hgap : fiveRegionGap r*(A^7*B^5*S^3) < C := hgapBoth.1
  have hgapbs : (fiveRegionCoupledGap r*Rbs)*(A^7*B^5*S^3) < C := hgapBoth.2
  have hfront : 2*A*B*S < T :=
    (IsD1Tuple.small_norm_retained_parameters hK phi b4 hb4 (hmon.comp hm4)
      hN8 hB (fiveRegion_case_disjunction r A B hcase)).1
  have hTBS : 2*B*S < T := by
    have hh := mul_le_mul_of_nonneg_right hA1 (show 0 ≤ 2*B*S by positivity)
    nlinarith only [hh,hfront]
  have hC0 : 0 < C := by linarith only [hC1000]
  have hC200S : 200*S ≤ C := hC200S'.le
  have hC200B : 200*B ≤ C := (by gcongr : 200*B ≤ 200*S).trans hC200S
  have hC4T : 4*T ≤ C := hC4T'.le
  have hC4S : 4*S ≤ C := (by gcongr : 4*S ≤ 4*T).trans hC4T
  have hC4B : 4*B < C := by linarith only [hC200B,hB0]
  have hAC : 1000 ≤ A*C := by
    have hh := mul_le_mul_of_nonneg_right hA1 hC0.le
    linarith only [hh,hC1000]
  have hBC : 1000 ≤ B*C := hAC.trans (mul_le_mul_of_nonneg_right hAB hC0.le)
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
  have hQ : ¬ ((allLargeWindowQ A T C).1 ≤ D ∧ D ≤ (allLargeWindowQ A T C).2) := by
    rintro ⟨hl,hu⟩
    exact full_ring_finiteQ_closed_interval_excluded hK phi hTup b4 (a 4) (a 5)
      (fun j => hmem (i4 j)) (hmem 4) (hmem 5) hb4.1
      (fun j => ha.1.ne (by fin_cases j <;> decide))
      (fun j => ha.1.ne (by fin_cases j <;> decide))
      (ha.1.ne (by decide : (4 : Fin 6) ≠ 5)) A T hA0
      (fun j => hmon (by fin_cases j <;> decide))
      (fun j => hmon (by fin_cases j <;> decide)) hC4T hCD hAC hl hu
  have hN2 : ¬ ((commonWindowN2 A B C (fiveRegionN2Height r) (fiveRegionN2Residual r)).1 ≤ D ∧ D ≤ (commonWindowN2 A B C (fiveRegionN2Height r) (fiveRegionN2Residual r)).2) := by
    rintro ⟨hl,hu⟩
    exact full_ring_finiteN2_five_region_interval_excluded hK phi hTup (a 0) (a 1) (a 4) (a 5)
      (hmem 0) (hmem 1) (hmem 4) (hmem 5)
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      hAB hC1000.le hC200B hCD r hc.2.2.2.2.2 hl hu
  have hN3 : ¬ ((commonWindowN3 A B C (fiveRegionN3Height r) (fiveRegionN3Residual r)).1 ≤ D ∧ D ≤ (commonWindowN3 A B C (fiveRegionN3Height r) (fiveRegionN3Residual r)).2) := by
    rintro ⟨hl,hu⟩
    exact full_ring_finiteN3_five_region_interval_excluded hK phi hTup (a 0) (a 1) (a 4) (a 5)
      (hmem 0) (hmem 1) (hmem 4) (hmem 5)
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      hAB hC1000.le hC200B hCD r hc.2.2.2.2.2 hl hu
  have hA3 : ¬ ((commonWindowA3 A B C (fiveRegionA3Height r) (fiveRegionA3Residual r)).1 ≤ D ∧ D ≤ (commonWindowA3 A B C (fiveRegionA3Height r) (fiveRegionA3Residual r)).2) := by
    rintro ⟨hl,hu⟩
    exact full_ring_finiteA3_five_region_interval_excluded hK phi hTup (a 0) (a 1) (a 4) (a 5)
      (hmem 0) (hmem 1) (hmem 4) (hmem 5)
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      hAB hC1000.le hC200B hCD r hc.2.2.2.2.2 hl hu
  have hA4 : ¬ ((commonWindowA4 A B C (fiveRegionA4Height r) (fiveRegionA4Residual r)).1 ≤ D ∧ D ≤ (commonWindowA4 A B C (fiveRegionA4Height r) (fiveRegionA4Residual r)).2) := by
    rintro ⟨hl,hu⟩
    exact full_ring_finiteA4_five_region_interval_excluded hK phi hTup (a 0) (a 1) (a 4) (a 5)
      (hmem 0) (hmem 1) (hmem 4) (hmem 5)
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      hAB hC1000.le hC200B hCD r hc.2.2.2.2.2 hl hu
  have hA5 : ¬ ((commonWindowA5 A B C (fiveRegionA5Height r) (fiveRegionA5Residual r)).1 ≤ D ∧ D ≤ (commonWindowA5 A B C (fiveRegionA5Height r) (fiveRegionA5Residual r)).2) := by
    rintro ⟨hl,hu⟩
    exact full_ring_finiteA5_five_region_interval_excluded hK phi hTup (a 0) (a 1) (a 4) (a 5)
      (hmem 0) (hmem 1) (hmem 4) (hmem 5)
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      hAB hC1000.le hC200B hCD r hc.2.2.2.2.2 hl hu
  have hN3bs : ¬ ((commonWindowN3 B S C 4143 Rbs).1 ≤ D ∧ D ≤ (commonWindowN3 B S C 4143 Rbs).2) := by
    rintro ⟨hl,hu⟩
    exact full_ring_finiteN3_phi_interval_excluded hK phi hTup (a 1) (a 2) (a 4) (a 5)
      (hmem 1) (hmem 2) (hmem 4) (hmem 5)
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      (ha.1.ne (by decide)) (ha.1.ne (by decide)) (ha.1.ne (by decide))
      hBS hC1000.le hC200S hCD hl hu
  have hP : ¬ ((commonWindowP A B S C (fiveRegionPResidual r)).1 ≤ D ∧
      D ≤ (commonWindowP A B S C (fiveRegionPResidual r)).2) := by
    rintro ⟨hl,hu⟩
    exact full_ring_finiteP_five_region_interval_excluded hK phi hTup b3 (a 4) (a 5)
      (fun j => hmem (i3 j)) (hmem 4) (hmem 5) hb3.1
      (fun j => ha.1.ne (by fin_cases j <;> decide))
      (fun j => ha.1.ne (by fin_cases j <;> decide))
      (ha.1.ne (by decide : (4 : Fin 6) ≠ 5)) (hmon.comp hm3) hC200S hCD hAC
      r hc.2.2.2.2.1 hl hu
  have hM : ¬ ((allLargeWindowM A B S C).1 ≤ D ∧ D ≤ (allLargeWindowM A B S C).2) := by
    rintro ⟨hl,hu⟩
    exact full_ring_finiteM_closed_interval_excluded hK phi hTup b3 (a 4) (a 5)
      (fun j => hmem (i3 j)) (hmem 4) (hmem 5) hb3.1
      (fun j => ha.1.ne (by fin_cases j <;> decide))
      (fun j => ha.1.ne (by fin_cases j <;> decide))
      (ha.1.ne (by decide : (4 : Fin 6) ≠ 5)) (hmon.comp hm3) hC4S hCD hAC hl hu
  have hpGap : 0 < fiveRegionGap r := by
    fin_cases r <;> norm_num [fiveRegionGap,fiveRegionAnchorRatio]
  have hpCoupledGap : 0 < fiveRegionCoupledGap r := by
    fin_cases r <;> norm_num [fiveRegionCoupledGap,fiveRegionAnchorRatio]
  have hpN2Height : 0 < fiveRegionN2Height r := by
    fin_cases r <;> norm_num [fiveRegionN2Height,fiveRegionAnchorRatio]
  have hpN3Height : 0 < fiveRegionN3Height r := by
    fin_cases r <;> norm_num [fiveRegionN3Height,fiveRegionAnchorRatio]
  have hpA3Height : 0 < fiveRegionA3Height r := by
    fin_cases r <;> norm_num [fiveRegionA3Height,fiveRegionAnchorRatio]
  have hpA4Height : 0 < fiveRegionA4Height r := by
    fin_cases r <;> norm_num [fiveRegionA4Height,fiveRegionAnchorRatio]
  have hpA5Height : 0 < fiveRegionA5Height r := by
    fin_cases r <;> norm_num [fiveRegionA5Height,fiveRegionAnchorRatio]
  have hpN2Residual : 0 < fiveRegionN2Residual r := by
    fin_cases r <;> norm_num [fiveRegionN2Residual,fiveRegionAnchorRatio]
  have hpN3Residual : 0 < fiveRegionN3Residual r := by
    fin_cases r <;> norm_num [fiveRegionN3Residual,fiveRegionAnchorRatio]
  have hpA3Residual : 0 < fiveRegionA3Residual r := by
    fin_cases r <;> norm_num [fiveRegionA3Residual,fiveRegionAnchorRatio]
  have hpA4Residual : 0 < fiveRegionA4Residual r := by
    fin_cases r <;> norm_num [fiveRegionA4Residual,fiveRegionAnchorRatio]
  have hpA5Residual : 0 < fiveRegionA5Residual r := by
    fin_cases r <;> norm_num [fiveRegionA5Residual,fiveRegionAnchorRatio]
  have hpPResidual : 0 < fiveRegionPResidual r := by
    fin_cases r <;> norm_num [fiveRegionPResidual,fiveRegionAnchorRatio]
  have hRbs : 0 < Rbs := by
    have hsep : phi (a 1 : K)-phi (a 2 : K) ≠ 0 := by
      intro hh
      apply ha.1.ne (by decide : (1 : Fin 6) ≠ 2)
      apply NumberField.RingOfIntegers.ext
      exact phi.injective (sub_eq_zero.mp hh)
    have hd : 0 < ‖phi (a 1 : K)-phi (a 2 : K)‖ := norm_pos_iff.mpr hsep
    have hPhi : 0 < phasePhi (phi (a 1 : K)) (phi (a 2 : K)) := by
      apply lt_of_lt_of_le (pow_pos (div_pos hd hS0) 6)
      exact le_max_left _ _
    dsimp [Rbs]
    positivity
  have hnum := fiveRegion_common_overlap_bounds r A B S hc.1 hc.2.2.1 hBS
  rcases common_interval_window_overlaps A B S T C
      (fiveRegionGap r) (fiveRegionCoupledGap r) 1
      (fiveRegionN2Height r) (fiveRegionN3Height r) (fiveRegionA3Height r)
      (fiveRegionA4Height r) (fiveRegionA5Height r) 4143
      (fiveRegionN2Residual r) (fiveRegionN3Residual r) (fiveRegionA3Residual r)
      (fiveRegionA4Residual r) (fiveRegionA5Residual r) Rbs (fiveRegionPResidual r)
      hA0 hB0 hS0 hBS hpGap hpCoupledGap (by norm_num)
      hpN2Height hpN3Height hpA3Height hpA4Height hpA5Height (by norm_num)
      hpN2Residual hpN3Residual hpA3Residual hpA4Residual hpA5Residual hRbs hpPResidual
      hTBS (by simpa only [one_mul] using hCgap) hgap hgapbs hnum with
    ⟨hoStart,hoQN2,hoN2P,hoPN3,hoPA3,hoA3M,hoMN3,hoN3A4,hoN3bs,hoBsA4,
      hoA4O4,hoO4A5,hoA5O5,hoO5O6,hoRate⟩
  have hQlower : (allLargeWindowQ A T C).1 ≤ D := (hoStart.trans hDstart).le
  have hQupper : (allLargeWindowQ A T C).2 < D := window_upper_lt_of_excluded _ D hQ hQlower
  have hN2upper : (commonWindowN2 A B C (fiveRegionN2Height r) (fiveRegionN2Residual r)).2 < D :=
    window_upper_lt_of_excluded _ D hN2 (hoQN2.trans hQupper).le
  have hPlower : (commonWindowP A B S C (fiveRegionPResidual r)).1 ≤ D := (hoN2P.trans hN2upper).le
  have hPupper : (commonWindowP A B S C (fiveRegionPResidual r)).2 < D := window_upper_lt_of_excluded _ D hP hPlower
  have hN3lower : (commonWindowN3 A B C (fiveRegionN3Height r) (fiveRegionN3Residual r)).1 ≤ D := by
    by_cases hcase : B^2 ≤ S
    · exact ((hoPN3 hcase).trans hPupper).le
    · have hA3upper := window_upper_lt_of_excluded _ D hA3 (hoPA3.trans hPupper).le
      have hMupper := window_upper_lt_of_excluded _ D hM
        ((hoA3M (le_of_not_ge hcase)).trans hA3upper).le
      exact (hoMN3.trans hMupper).le
  have hN3upper := window_upper_lt_of_excluded _ D hN3 hN3lower
  have hA4lower : (commonWindowA4 A B C (fiveRegionA4Height r) (fiveRegionA4Residual r)).1 ≤ D := by
    by_cases hcase : B^3 ≤ S
    · exact ((hoN3A4 hcase).trans hN3upper).le
    · have hbsUpper := window_upper_lt_of_excluded _ D hN3bs
        ((hoN3bs (le_of_not_ge hcase)).trans hN3upper).le
      exact (hoBsA4.trans hbsUpper).le
  have hA4upper := window_upper_lt_of_excluded _ D hA4 hA4lower
  have hO4lower : ordinaryWindowLower B C 4 ≤ D := (hoA4O4.trans hA4upper).le
  have hO4upper : ordinaryWindowUpper A B C 4 < D := by
    apply lt_of_not_ge
    intro h
    exact IsD1Tuple.ordinary_closed_interval_excluded hK phi tAB htAB
      hAB hAC hC4B hCD 4 (by norm_num) hO4lower h
  have hA5upper := window_upper_lt_of_excluded _ D hA5 (hoO4A5.trans hO4upper).le
  have hO5lower : ordinaryWindowLower B C 5 ≤ D := (hoA5O5.trans hA5upper).le
  exact IsD1Tuple.ordinary_tail_incompatible hK phi tAB htAB hAB hAC hC4B hCD
    hoRate hoO5O6.le hO5lower

end D1Bound5
end
