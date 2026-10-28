-- Prove2me | solution 1 for D1Bound5.all_large_window_overlaps
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:17:45.439446+00:00
-- url     : https://prove2.me/submissions/821bb36b-288e-43da-bd16-65874e9c8493

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
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
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_AllLargeWindows_Definitions
import Definitions.Def_D1Bound5_OrdinaryClosedIntervals_Definitions
import Theorems.Thm_D1Bound5_all_large_overlap_constants
import Theorems.Thm_D1Bound5_window_overlap_of_ratio

section
namespace D1Bound5

/-- All actual endpoint overlaps in the all-large branch, including
both optional detours. The finite families are numerical expressions here;
the final theorem supplies their genuine full-ring exclusions. -/
theorem _root_.solution
    (A B S T C : ℝ) (hA : 3 ≤ A) (hAB : A ≤ B) (hBS : B ≤ S)
    (hT : 2*B*S < T) (hC : A^2*T^5/S^2 < C)
    (hgap : 400*(A^7*B^5*S^3) < C) :
    (allLargeWindowQ A T C).1 < A^2*C^7/(S^2*T^4) ∧
    (allLargeWindowN2 A B C).1 < (allLargeWindowQ A T C).2 ∧
    (allLargeWindowP A B S C).1 < (allLargeWindowN2 A B C).2 ∧
    (B^2 ≤ S → (allLargeWindowN3 A B C).1 < (allLargeWindowP A B S C).2) ∧
    (allLargeWindowA3 A B C).1 < (allLargeWindowP A B S C).2 ∧
    (S ≤ B^2 → (allLargeWindowM A B S C).1 < (allLargeWindowA3 A B C).2) ∧
    (allLargeWindowN3 A B C).1 < (allLargeWindowM A B S C).2 ∧
    (B^3 ≤ S → (allLargeWindowA4 A B C).1 < (allLargeWindowN3 A B C).2) ∧
    (S ≤ B^3 → (allLargeWindowN3 B S C).1 < (allLargeWindowN3 A B C).2) ∧
    (allLargeWindowA4 A B C).1 < (allLargeWindowN3 B S C).2 ∧
    ordinaryWindowLower B C 4 < (allLargeWindowA4 A B C).2 ∧
    (allLargeWindowA5 A B C).1 < ordinaryWindowUpper A B C 4 ∧
    ordinaryWindowLower B C 5 < (allLargeWindowA5 A B C).2 ∧
    ordinaryWindowLower B C 6 < ordinaryWindowUpper A B C 5 ∧
    42*B^3*C < 2*A*C^2/(5*B) := by
  have hB : 3 ≤ B := hA.trans hAB
  have hS : 3 ≤ S := hB.trans hBS
  have hA0 : 0 < A := by linarith only [hA]
  have hB0 : 0 < B := by linarith only [hB]
  have hS0 : 0 < S := by linarith only [hS]
  have hT0 : 0 < T := lt_trans (by positivity) hT
  have hbase0 : 0 < 400*(A^7*B^5*S^3) := by positivity
  have hC0 : 0 < C := hbase0.trans hgap
  have hCbase0 : 0 < A^2*T^5/S^2 := by positivity
  rcases all_large_overlap_constants A B S hA hB hS with
    ⟨hn0,hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8,hn9,hn10,hn11,hn12,hn13,hn14,hn15⟩
  have hq0 : 1 < (1024*(1-1/4000 : ℝ)/12100)*(A^10*B^10) := by
    have hh : (13/10 : ℝ) < (1024*(1-1/4000 : ℝ)/12100)*(A^10*B^10) := by
      convert hn0 using 1 <;> norm_num <;> ring
    exact lt_trans (by norm_num) hh
  have hr0 : 1 < A^2*C^4*(1-1/4000 : ℝ)/(12100*S^2*T^10) := by
    calc
      (1 : ℝ) < (1024*(1-1/4000 : ℝ)/12100)*(A^10*B^10) := hq0
      _ = (1-1/4000 : ℝ)*A^10*(2*B*S)^10/(12100*S^10) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ (1-1/4000 : ℝ)*A^10*T^10/(12100*S^10) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | positivity
      _ = A^2*(A^2*T^5/S^2)^4*(1-1/4000 : ℝ)/(12100*S^2*T^10) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ A^2*C^4*(1-1/4000 : ℝ)/(12100*S^2*T^10) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | positivity
  have hq1 : 1 < (256/(36*243^2*(4001/3999 : ℝ)))*(A^8*S^4) := by
    have hh : (13/10 : ℝ) < (256/(36*243^2*(4001/3999 : ℝ)))*(A^8*S^4) := by
      convert hn1 using 1 <;> norm_num <;> ring
    exact lt_trans (by norm_num) hh
  have hr1 : 1 < A^4*C^2/(36*243^2*B^8*T^2*(4001/3999 : ℝ)) := by
    calc
      (1 : ℝ) < (256/(36*243^2*(4001/3999 : ℝ)))*(A^8*S^4) := hq1
      _ = A^8*(2*B*S)^8/(36*243^2*B^8*S^4*(4001/3999 : ℝ)) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ A^8*T^8/(36*243^2*B^8*S^4*(4001/3999 : ℝ)) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | positivity
      _ = A^4*(A^2*T^5/S^2)^2/(36*243^2*B^8*T^2*(4001/3999 : ℝ)) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ A^4*C^2/(36*243^2*B^8*T^2*(4001/3999 : ℝ)) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | positivity
  have hq2 : 1 < (400^2/(16*(5/4 : ℝ)^2*2400^2*(4001/3999 : ℝ)))*(A^20*B^4) := by
    have hh : (13/10 : ℝ) < (400^2/(16*(5/4 : ℝ)^2*2400^2*(4001/3999 : ℝ)))*(A^20*B^4) := by
      convert hn2 using 1 <;> norm_num <;> ring
    exact lt_trans (by norm_num) hh
  have hr2 : 1 < A^6*C^2/((16*(5/4 : ℝ)^2*2400^2*(4001/3999 : ℝ))*B^6*S^6) := by
    calc
      (1 : ℝ) < (400^2/(16*(5/4 : ℝ)^2*2400^2*(4001/3999 : ℝ)))*(A^20*B^4) := hq2
      _ = A^6*(400*(A^7*B^5*S^3))^2/((16*(5/4 : ℝ)^2*2400^2*(4001/3999 : ℝ))*B^6*S^6) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ A^6*C^2/((16*(5/4 : ℝ)^2*2400^2*(4001/3999 : ℝ))*B^6*S^6) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | positivity
  have hq3 : 1 < (400^2/(16*(5/4 : ℝ)^2*2400^2*(4001/3999 : ℝ)))*(A^20*S^2) := by
    have hh : (13/10 : ℝ) < (400^2/(16*(5/4 : ℝ)^2*2400^2*(4001/3999 : ℝ)))*(A^20*S^2) := by
      convert hn3 using 1 <;> norm_num <;> ring
    exact lt_trans (by norm_num) hh
  have hr3 : 1 < A^6*C^2/((16*(5/4 : ℝ)^2*2400^2*(4001/3999 : ℝ))*B^10*S^4) := by
    calc
      (1 : ℝ) < (400^2/(16*(5/4 : ℝ)^2*2400^2*(4001/3999 : ℝ)))*(A^20*S^2) := hq3
      _ = A^6*(400*(A^7*B^5*S^3))^2/((16*(5/4 : ℝ)^2*2400^2*(4001/3999 : ℝ))*B^10*S^4) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ A^6*C^2/((16*(5/4 : ℝ)^2*2400^2*(4001/3999 : ℝ))*B^10*S^4) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | positivity
  have hq4 : 1 < (400^2/(16*(3 : ℝ)^2*4143^2*(4001/3999 : ℝ)))*(A^20) := by
    have hh : (13/10 : ℝ) < (400^2/(16*(3 : ℝ)^2*4143^2*(4001/3999 : ℝ)))*(A^20) := by
      convert hn4 using 1 <;> norm_num <;> ring
    exact lt_trans (by norm_num) hh
  have hr4 (hextra : B^2 ≤ S) : 1 < A^6*C^2/((16*(3 : ℝ)^2*4143^2*(4001/3999 : ℝ))*B^14*S^4) := by
    calc
      (1 : ℝ) < (400^2/(16*(3 : ℝ)^2*4143^2*(4001/3999 : ℝ)))*(A^20) := hq4
      _ = 400^2*A^20*(B^2)^2/((16*(3 : ℝ)^2*4143^2*(4001/3999 : ℝ))*B^4) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ 400^2*A^20*S^2/((16*(3 : ℝ)^2*4143^2*(4001/3999 : ℝ))*B^4) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | exact hextra | positivity
      _ = A^6*(400*(A^7*B^5*S^3))^2/((16*(3 : ℝ)^2*4143^2*(4001/3999 : ℝ))*B^14*S^4) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ A^6*C^2/((16*(3 : ℝ)^2*4143^2*(4001/3999 : ℝ))*B^14*S^4) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | exact hextra | positivity
  have hq5 : 1 < (400^2/(16*(3 : ℝ)^2*2265^2*(4001/3999 : ℝ)))*(A^20) := by
    have hh : (13/10 : ℝ) < (400^2/(16*(3 : ℝ)^2*2265^2*(4001/3999 : ℝ)))*(A^20) := by
      convert hn5 using 1 <;> norm_num <;> ring
    exact lt_trans (by norm_num) hh
  have hr5 : 1 < A^6*C^2/((16*(3 : ℝ)^2*2265^2*(4001/3999 : ℝ))*B^12*S^4) := by
    calc
      (1 : ℝ) < (400^2/(16*(3 : ℝ)^2*2265^2*(4001/3999 : ℝ)))*(A^20) := hq5
      _ = 400^2*A^20*B^2/((16*(3 : ℝ)^2*2265^2*(4001/3999 : ℝ))*B^2) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ 400^2*A^20*S^2/((16*(3 : ℝ)^2*2265^2*(4001/3999 : ℝ))*B^2) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | positivity
      _ = A^6*(400*(A^7*B^5*S^3))^2/((16*(3 : ℝ)^2*2265^2*(4001/3999 : ℝ))*B^12*S^4) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ A^6*C^2/((16*(3 : ℝ)^2*2265^2*(4001/3999 : ℝ))*B^12*S^4) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | positivity
  have hq6 : 1 < (400^4/(16*(35/16 : ℝ)^2*((8/9 : ℝ)*608^2)^2*(4001/3999 : ℝ)))*(A^36) := by
    have hh : (13/10 : ℝ) < (400^4/(16*(35/16 : ℝ)^2*((8/9 : ℝ)*608^2)^2*(4001/3999 : ℝ)))*(A^36) := by
      convert hn6 using 1 <;> norm_num <;> ring
    exact lt_trans (by norm_num) hh
  have hr6 (hextra : S ≤ B^2) : 1 < A^8*C^4/((16*(35/16 : ℝ)^2*((8/9 : ℝ)*608^2)^2*(4001/3999 : ℝ))*B^12*S^16) := by
    calc
      (1 : ℝ) < (400^4/(16*(35/16 : ℝ)^2*((8/9 : ℝ)*608^2)^2*(4001/3999 : ℝ)))*(A^36) := hq6
      _ = 400^4*A^36*S^4/((16*(35/16 : ℝ)^2*((8/9 : ℝ)*608^2)^2*(4001/3999 : ℝ))*S^4) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ 400^4*A^36*(B^2)^4/((16*(35/16 : ℝ)^2*((8/9 : ℝ)*608^2)^2*(4001/3999 : ℝ))*S^4) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | exact hextra | positivity
      _ = A^8*(400*(A^7*B^5*S^3))^4/((16*(35/16 : ℝ)^2*((8/9 : ℝ)*608^2)^2*(4001/3999 : ℝ))*B^12*S^16) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ A^8*C^4/((16*(35/16 : ℝ)^2*((8/9 : ℝ)*608^2)^2*(4001/3999 : ℝ))*B^12*S^16) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | exact hextra | positivity
  have hq7 : 1 < (400^4/(16*(3920/81 : ℝ)^2*4143^2*(4001/3999 : ℝ)))*(A^34*B^2*S^2) := by
    have hh : (13/10 : ℝ) < (400^4/(16*(3920/81 : ℝ)^2*4143^2*(4001/3999 : ℝ)))*(A^34*B^2*S^2) := by
      convert hn7 using 1 <;> norm_num <;> ring
    exact lt_trans (by norm_num) hh
  have hr7 : 1 < A^6*C^4/((16*(3920/81 : ℝ)^2*4143^2*(4001/3999 : ℝ))*B^18*S^10) := by
    calc
      (1 : ℝ) < (400^4/(16*(3920/81 : ℝ)^2*4143^2*(4001/3999 : ℝ)))*(A^34*B^2*S^2) := hq7
      _ = A^6*(400*(A^7*B^5*S^3))^4/((16*(3920/81 : ℝ)^2*4143^2*(4001/3999 : ℝ))*B^18*S^10) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ A^6*C^4/((16*(3920/81 : ℝ)^2*4143^2*(4001/3999 : ℝ))*B^18*S^10) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | positivity
  have hq8 : 1 < (400^2/(16*(35/32 : ℝ)^2*165763^2*(4001/3999 : ℝ)))*(A^22*B^4) := by
    have hh : (13/10 : ℝ) < (400^2/(16*(35/32 : ℝ)^2*165763^2*(4001/3999 : ℝ)))*(A^22*B^4) := by
      convert hn8 using 1 <;> norm_num <;> ring
    exact lt_trans (by norm_num) hh
  have hr8 (hextra : B^3 ≤ S) : 1 < A^8*C^2/((16*(35/32 : ℝ)^2*165763^2*(4001/3999 : ℝ))*B^24) := by
    calc
      (1 : ℝ) < (400^2/(16*(35/32 : ℝ)^2*165763^2*(4001/3999 : ℝ)))*(A^22*B^4) := hq8
      _ = 400^2*A^22*(B^3)^6/((16*(35/32 : ℝ)^2*165763^2*(4001/3999 : ℝ))*B^14) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ 400^2*A^22*S^6/((16*(35/32 : ℝ)^2*165763^2*(4001/3999 : ℝ))*B^14) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | exact hextra | positivity
      _ = A^8*(400*(A^7*B^5*S^3))^2/((16*(35/32 : ℝ)^2*165763^2*(4001/3999 : ℝ))*B^24) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ A^8*C^2/((16*(35/32 : ℝ)^2*165763^2*(4001/3999 : ℝ))*B^24) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | exact hextra | positivity
  have hq9 : 1 < (400^4/(16*(35/32 : ℝ)^2*4143^2*(4001/3999 : ℝ)))*(A^36*B^8) := by
    have hh : (13/10 : ℝ) < (400^4/(16*(35/32 : ℝ)^2*4143^2*(4001/3999 : ℝ)))*(A^36*B^8) := by
      convert hn9 using 1 <;> norm_num <;> ring
    exact lt_trans (by norm_num) hh
  have hr9 (hextra : S ≤ B^3) : 1 < A^8*C^4/((16*(35/32 : ℝ)^2*4143^2*(4001/3999 : ℝ))*B^6*S^14) := by
    calc
      (1 : ℝ) < (400^4/(16*(35/32 : ℝ)^2*4143^2*(4001/3999 : ℝ)))*(A^36*B^8) := hq9
      _ = 400^4*A^36*B^8*S^2/((16*(35/32 : ℝ)^2*4143^2*(4001/3999 : ℝ))*S^2) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ 400^4*A^36*B^8*(B^3)^2/((16*(35/32 : ℝ)^2*4143^2*(4001/3999 : ℝ))*S^2) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | exact hextra | positivity
      _ = A^8*(400*(A^7*B^5*S^3))^4/((16*(35/32 : ℝ)^2*4143^2*(4001/3999 : ℝ))*B^6*S^14) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ A^8*C^4/((16*(35/32 : ℝ)^2*4143^2*(4001/3999 : ℝ))*B^6*S^14) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | exact hextra | positivity
  have hq10 : 1 < (400^2/(16*(35/32 : ℝ)^2*165763^2*(4001/3999 : ℝ)))*(A^14) := by
    have hh : (7/5 : ℝ) < (400^2/(16*(35/32 : ℝ)^2*165763^2*(4001/3999 : ℝ)))*(A^14) := by
      convert hn10 using 1 <;> norm_num <;> ring
    exact lt_trans (by norm_num) hh
  have hr10 : 1 < 1*C^2/((16*(35/32 : ℝ)^2*165763^2*(4001/3999 : ℝ))*B^10*S^6) := by
    calc
      (1 : ℝ) < (400^2/(16*(35/32 : ℝ)^2*165763^2*(4001/3999 : ℝ)))*(A^14) := hq10
      _ = 1*(400*(A^7*B^5*S^3))^2/((16*(35/32 : ℝ)^2*165763^2*(4001/3999 : ℝ))*B^10*S^6) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ 1*C^2/((16*(35/32 : ℝ)^2*165763^2*(4001/3999 : ℝ))*B^10*S^6) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | positivity
  have hq11 : 1 < (400^4/(144*(63/8 : ℝ)^2*42^8*(4001/3999 : ℝ)))*(A^38*B^2) := by
    have hh : (13/10 : ℝ) < (400^4/(144*(63/8 : ℝ)^2*42^8*(4001/3999 : ℝ)))*(A^38*B^2) := by
      convert hn11 using 1 <;> norm_num <;> ring
    exact lt_trans (by norm_num) hh
  have hr11 : 1 < A^10*C^4/((144*(63/8 : ℝ)^2*42^8*(4001/3999 : ℝ))*B^30) := by
    calc
      (1 : ℝ) < (400^4/(144*(63/8 : ℝ)^2*42^8*(4001/3999 : ℝ)))*(A^38*B^2) := hq11
      _ = 400^4*A^38*B^12/((144*(63/8 : ℝ)^2*42^8*(4001/3999 : ℝ))*B^10) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ 400^4*A^38*S^12/((144*(63/8 : ℝ)^2*42^8*(4001/3999 : ℝ))*B^10) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | positivity
      _ = A^10*(400*(A^7*B^5*S^3))^4/((144*(63/8 : ℝ)^2*42^8*(4001/3999 : ℝ))*B^30) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ A^10*C^4/((144*(63/8 : ℝ)^2*42^8*(4001/3999 : ℝ))*B^30) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | positivity
  have hq12 : 1 < (400^4/(4*3113013^2*(5/2 : ℝ)^8*(4001/3999 : ℝ)))*(A^36) := by
    have hh : (13/10 : ℝ) < (400^4/(4*3113013^2*(5/2 : ℝ)^8*(4001/3999 : ℝ)))*(A^36) := by
      convert hn12 using 1 <;> norm_num <;> ring
    exact lt_trans (by norm_num) hh
  have hr12 : 1 < A^8*C^4/((4*3113013^2*(5/2 : ℝ)^8*(4001/3999 : ℝ))*B^32) := by
    calc
      (1 : ℝ) < (400^4/(4*3113013^2*(5/2 : ℝ)^8*(4001/3999 : ℝ)))*(A^36) := hq12
      _ = 400^4*A^36*B^12/((4*3113013^2*(5/2 : ℝ)^8*(4001/3999 : ℝ))*B^12) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ 400^4*A^36*S^12/((4*3113013^2*(5/2 : ℝ)^8*(4001/3999 : ℝ))*B^12) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | positivity
      _ = A^8*(400*(A^7*B^5*S^3))^4/((4*3113013^2*(5/2 : ℝ)^8*(4001/3999 : ℝ))*B^32) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ A^8*C^4/((4*3113013^2*(5/2 : ℝ)^8*(4001/3999 : ℝ))*B^32) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | positivity
  have hq13 : 1 < (400^6/(144*(495/64 : ℝ)^2*42^10*(4001/3999 : ℝ)))*(A^54*B^10) := by
    have hh : (13/10 : ℝ) < (400^6/(144*(495/64 : ℝ)^2*42^10*(4001/3999 : ℝ)))*(A^54*B^10) := by
      convert hn13 using 1 <;> norm_num <;> ring
    exact lt_trans (by norm_num) hh
  have hr13 : 1 < A^12*C^6/((144*(495/64 : ℝ)^2*42^10*(4001/3999 : ℝ))*B^38) := by
    calc
      (1 : ℝ) < (400^6/(144*(495/64 : ℝ)^2*42^10*(4001/3999 : ℝ)))*(A^54*B^10) := hq13
      _ = 400^6*A^54*B^18/((144*(495/64 : ℝ)^2*42^10*(4001/3999 : ℝ))*B^8) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ 400^6*A^54*S^18/((144*(495/64 : ℝ)^2*42^10*(4001/3999 : ℝ))*B^8) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | positivity
      _ = A^12*(400*(A^7*B^5*S^3))^6/((144*(495/64 : ℝ)^2*42^10*(4001/3999 : ℝ))*B^38) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ A^12*C^6/((144*(495/64 : ℝ)^2*42^10*(4001/3999 : ℝ))*B^38) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | positivity
  have hq14 : 1 < (400^6/(36*42^12*(5/2 : ℝ)^10*(4001/3999 : ℝ)))*(A^52*B^4) := by
    have hh : (13/10 : ℝ) < (400^6/(36*42^12*(5/2 : ℝ)^10*(4001/3999 : ℝ)))*(A^52*B^4) := by
      convert hn14 using 1 <;> norm_num <;> ring
    exact lt_trans (by norm_num) hh
  have hr14 : 1 < A^10*C^6/((36*42^12*(5/2 : ℝ)^10*(4001/3999 : ℝ))*B^44) := by
    calc
      (1 : ℝ) < (400^6/(36*42^12*(5/2 : ℝ)^10*(4001/3999 : ℝ)))*(A^52*B^4) := hq14
      _ = 400^6*A^52*B^18/((36*42^12*(5/2 : ℝ)^10*(4001/3999 : ℝ))*B^14) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ 400^6*A^52*S^18/((36*42^12*(5/2 : ℝ)^10*(4001/3999 : ℝ))*B^14) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | positivity
      _ = A^10*(400*(A^7*B^5*S^3))^6/((36*42^12*(5/2 : ℝ)^10*(4001/3999 : ℝ))*B^44) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ A^10*C^6/((36*42^12*(5/2 : ℝ)^10*(4001/3999 : ℝ))*B^44) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | positivity
  have hq15 : 1 < (400/(105))*(A^8*B*S^3) := by
    have hh : (13/10 : ℝ) < (400/(105))*(A^8*B*S^3) := by
      convert hn15 using 1 <;> norm_num <;> ring
    exact lt_trans (by norm_num) hh
  have hr15 : 1 < A*C^1/((105)*B^4) := by
    calc
      (1 : ℝ) < (400/(105))*(A^8*B*S^3) := hq15
      _ = A*(400*(A^7*B^5*S^3))^1/((105)*B^4) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne']
        <;> ring
      _ ≤ A*C^1/((105)*B^4) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hT.le | exact hBS | positivity
  have ho0 : (allLargeWindowQ A T C).1 < A^2*C^7/(S^2*T^4) := by
    apply window_overlap_of_ratio ((allLargeWindowQ A T C).1) (A^2*C^7/(S^2*T^4)) (A^2*C^4*(1-1/4000 : ℝ)/(12100*S^2*T^10))
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne']
      <;> ring
    · exact hr0
  have ho1 : (allLargeWindowN2 A B C).1 < (allLargeWindowQ A T C).2 := by
    apply window_overlap_of_ratio ((allLargeWindowN2 A B C).1) ((allLargeWindowQ A T C).2) (A^4*C^2/(36*243^2*B^8*T^2*(4001/3999 : ℝ)))
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne']
      <;> ring
    · exact hr1
  have ho2 : 4*2400^2*(B*S^3)^2*C^5/(1-1/4000 : ℝ) < (allLargeWindowN2 A B C).2 := by
    apply window_overlap_of_ratio (4*2400^2*(B*S^3)^2*C^5/(1-1/4000 : ℝ)) ((allLargeWindowN2 A B C).2) (A^6*C^2/((16*(5/4 : ℝ)^2*2400^2*(4001/3999 : ℝ))*B^6*S^6))
    ·
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne']
      <;> ring
    · exact hr2
  have ho3 : 4*2400^2*(B^3*S^2)^2*C^5/(1-1/4000 : ℝ) < (allLargeWindowN2 A B C).2 := by
    apply window_overlap_of_ratio (4*2400^2*(B^3*S^2)^2*C^5/(1-1/4000 : ℝ)) ((allLargeWindowN2 A B C).2) (A^6*C^2/((16*(5/4 : ℝ)^2*2400^2*(4001/3999 : ℝ))*B^10*S^4))
    ·
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne']
      <;> ring
    · exact hr3
  have ho4 (hextra : B^2 ≤ S) : (allLargeWindowN3 A B C).1 < (allLargeWindowP A B S C).2 := by
    apply window_overlap_of_ratio ((allLargeWindowN3 A B C).1) ((allLargeWindowP A B S C).2) (A^6*C^2/((16*(3 : ℝ)^2*4143^2*(4001/3999 : ℝ))*B^14*S^4))
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne']
      <;> ring
    · exact hr4 hextra
  have ho5 : (allLargeWindowA3 A B C).1 < (allLargeWindowP A B S C).2 := by
    apply window_overlap_of_ratio ((allLargeWindowA3 A B C).1) ((allLargeWindowP A B S C).2) (A^6*C^2/((16*(3 : ℝ)^2*2265^2*(4001/3999 : ℝ))*B^12*S^4))
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne']
      <;> ring
    · exact hr5
  have ho6 (hextra : S ≤ B^2) : (allLargeWindowM A B S C).1 < (allLargeWindowA3 A B C).2 := by
    apply window_overlap_of_ratio ((allLargeWindowM A B S C).1) ((allLargeWindowA3 A B C).2) (A^8*C^4/((16*(35/16 : ℝ)^2*((8/9 : ℝ)*608^2)^2*(4001/3999 : ℝ))*B^12*S^16))
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne']
      <;> ring
    · exact hr6 hextra
  have ho7 : (allLargeWindowN3 A B C).1 < (allLargeWindowM A B S C).2 := by
    apply window_overlap_of_ratio ((allLargeWindowN3 A B C).1) ((allLargeWindowM A B S C).2) (A^6*C^4/((16*(3920/81 : ℝ)^2*4143^2*(4001/3999 : ℝ))*B^18*S^10))
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne']
      <;> ring
    · exact hr7
  have ho8 (hextra : B^3 ≤ S) : (allLargeWindowA4 A B C).1 < (allLargeWindowN3 A B C).2 := by
    apply window_overlap_of_ratio ((allLargeWindowA4 A B C).1) ((allLargeWindowN3 A B C).2) (A^8*C^2/((16*(35/32 : ℝ)^2*165763^2*(4001/3999 : ℝ))*B^24))
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne']
      <;> ring
    · exact hr8 hextra
  have ho9 (hextra : S ≤ B^3) : (allLargeWindowN3 B S C).1 < (allLargeWindowN3 A B C).2 := by
    apply window_overlap_of_ratio ((allLargeWindowN3 B S C).1) ((allLargeWindowN3 A B C).2) (A^8*C^4/((16*(35/32 : ℝ)^2*4143^2*(4001/3999 : ℝ))*B^6*S^14))
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne']
      <;> ring
    · exact hr9 hextra
  have ho10 : (allLargeWindowA4 A B C).1 < (allLargeWindowN3 B S C).2 := by
    apply window_overlap_of_ratio ((allLargeWindowA4 A B C).1) ((allLargeWindowN3 B S C).2) (1*C^2/((16*(35/32 : ℝ)^2*165763^2*(4001/3999 : ℝ))*B^10*S^6))
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne']
      <;> ring
    · exact hr10
  have ho11 : ordinaryWindowLower B C 4 < (allLargeWindowA4 A B C).2 := by
    apply window_overlap_of_ratio (ordinaryWindowLower B C 4) ((allLargeWindowA4 A B C).2) (A^10*C^4/((144*(63/8 : ℝ)^2*42^8*(4001/3999 : ℝ))*B^30))
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne']
      <;> ring
    · exact hr11
  have ho12 : (allLargeWindowA5 A B C).1 < ordinaryWindowUpper A B C 4 := by
    apply window_overlap_of_ratio ((allLargeWindowA5 A B C).1) (ordinaryWindowUpper A B C 4) (A^8*C^4/((4*3113013^2*(5/2 : ℝ)^8*(4001/3999 : ℝ))*B^32))
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne']
      <;> ring
    · exact hr12
  have ho13 : ordinaryWindowLower B C 5 < (allLargeWindowA5 A B C).2 := by
    apply window_overlap_of_ratio (ordinaryWindowLower B C 5) ((allLargeWindowA5 A B C).2) (A^12*C^6/((144*(495/64 : ℝ)^2*42^10*(4001/3999 : ℝ))*B^38))
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne']
      <;> ring
    · exact hr13
  have ho14 : ordinaryWindowLower B C 6 < ordinaryWindowUpper A B C 5 := by
    apply window_overlap_of_ratio (ordinaryWindowLower B C 6) (ordinaryWindowUpper A B C 5) (A^10*C^6/((36*42^12*(5/2 : ℝ)^10*(4001/3999 : ℝ))*B^44))
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowN2,allLargeWindowP,allLargeWindowA3,allLargeWindowM,allLargeWindowN3,allLargeWindowA4,allLargeWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne']
      <;> ring
    · exact hr14
  have ho15 : 42*B^3*C < 2*A*C^2/(5*B) := by
    apply window_overlap_of_ratio (42*B^3*C) (2*A*C^2/(5*B)) (A*C^1/((105)*B^4))
    ·
      positivity
    ·
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne']
      <;> ring
    · exact hr15
  have hoP : (allLargeWindowP A B S C).1 < (allLargeWindowN2 A B C).2 := by
    rcases le_total (B*S^3) (B^3*S^2) with h | h
    · simpa only [allLargeWindowP,max_eq_right h] using ho3
    · simpa only [allLargeWindowP,max_eq_left h] using ho2
  exact ⟨ho0,ho1,hoP,ho4,ho5,ho6,ho7,ho8,ho9,ho10,ho11,ho12,ho13,ho14,ho15⟩

end D1Bound5
end
