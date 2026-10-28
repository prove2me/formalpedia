-- Prove2me | solution 1 for D1Bound5.common_interval_window_overlaps
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:45:20.342112+00:00
-- url     : https://prove2.me/submissions/dcb97a5f-c7b6-4d64-8bb9-4591bc501fb5

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
import Definitions.Def_D1Bound5_CommonIntervalWindows_Definitions
import Definitions.Def_D1Bound5_OrdinaryClosedIntervals_Definitions
import Theorems.Thm_D1Bound5_window_overlap_of_ratio

section
namespace D1Bound5

/-- Parameterized endpoint calculation for both the five unbounded
regions and the forty-one S≥15 first-pair regions. The relabeled N3
junction uses its pointwise coupled rho bound; K0 controls the stronger
retained starting coefficient. -/
theorem _root_.solution
    (A B S T C G rho K0 M2 Mn M3 M4 M5 Mbs R2 Rn R3 R4 R5 Rbs Rp : ℝ)
    (hA0 : 0 < A) (hB0 : 0 < B) (hS0 : 0 < S) (hBS : B ≤ S)
    (hG : 0 < G) (hrho : 0 < rho) (hK0 : 0 < K0)
    (hM2 : 0 < M2)
    (hMn : 0 < Mn)
    (hM3 : 0 < M3)
    (hM4 : 0 < M4)
    (hM5 : 0 < M5)
    (hMbs : 0 < Mbs)
    (hR2 : 0 < R2)
    (hRn : 0 < Rn)
    (hR3 : 0 < R3)
    (hR4 : 0 < R4)
    (hR5 : 0 < R5)
    (hRbs : 0 < Rbs)
    (hRp : 0 < Rp)
    (hT : 2*B*S < T) (hC : K0*A^2*T^5/S^2 < C)
    (hgap : G*(A^7*B^5*S^3) < C)
    (hgapbs : (rho*Rbs)*(A^7*B^5*S^3) < C)
    (hnum : CommonOverlapBounds A B S G rho K0 M2 Mn M3 M4 M5 Mbs R2 Rn R3 R4 R5 Rp) :
    (allLargeWindowQ A T C).1 < A^2*C^7/(S^2*T^4) ∧
    (commonWindowN2 A B C M2 R2).1 < (allLargeWindowQ A T C).2 ∧
    (commonWindowP A B S C Rp).1 < (commonWindowN2 A B C M2 R2).2 ∧
    (B^2 ≤ S → (commonWindowN3 A B C Mn Rn).1 < (commonWindowP A B S C Rp).2) ∧
    (commonWindowA3 A B C M3 R3).1 < (commonWindowP A B S C Rp).2 ∧
    (S ≤ B^2 → (allLargeWindowM A B S C).1 < (commonWindowA3 A B C M3 R3).2) ∧
    (commonWindowN3 A B C Mn Rn).1 < (allLargeWindowM A B S C).2 ∧
    (B^3 ≤ S → (commonWindowA4 A B C M4 R4).1 < (commonWindowN3 A B C Mn Rn).2) ∧
    (S ≤ B^3 → (commonWindowN3 B S C Mbs Rbs).1 < (commonWindowN3 A B C Mn Rn).2) ∧
    (commonWindowA4 A B C M4 R4).1 < (commonWindowN3 B S C Mbs Rbs).2 ∧
    ordinaryWindowLower B C 4 < (commonWindowA4 A B C M4 R4).2 ∧
    (commonWindowA5 A B C M5 R5).1 < ordinaryWindowUpper A B C 4 ∧
    ordinaryWindowLower B C 5 < (commonWindowA5 A B C M5 R5).2 ∧
    ordinaryWindowLower B C 6 < ordinaryWindowUpper A B C 5 ∧
    42*B^3*C < 2*A*C^2/(5*B) := by
  have hT0 : 0 < T := lt_trans (by positivity) hT
  have hbase0 : 0 < G*(A^7*B^5*S^3) := by positivity
  have hC0 : 0 < C := hbase0.trans hgap
  have hCbase0 : 0 < K0*A^2*T^5/S^2 := by positivity
  have hbsbase0 : 0 < (rho*Rbs)*(A^7*B^5*S^3) := by positivity
  rcases hnum with
    ⟨hq0,hq1,hq2,hq3,hq4,hq5,hq6,hq7,hq8,hq9,hq10,hq11,hq12,hq13,hq14,hq15⟩
  have hr0 : 1 < A^2*C^4*(1-1/4000 : ℝ)/(12100*S^2*T^10) := by
    calc
      (1 : ℝ) < (1024*K0^4*(1-1/4000 : ℝ)/12100)*(A^10*B^10) := hq0
      _ = (1-1/4000 : ℝ)*K0^4*A^10*(2*B*S)^10/(12100*S^10) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ (1-1/4000 : ℝ)*K0^4*A^10*T^10/(12100*S^10) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | positivity
      _ = A^2*(K0*A^2*T^5/S^2)^4*(1-1/4000 : ℝ)/(12100*S^2*T^10) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ A^2*C^4*(1-1/4000 : ℝ)/(12100*S^2*T^10) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | positivity
  have hr1 : 1 < A^4*C^2/(36*M2^2*B^8*T^2*(4001/3999 : ℝ)) := by
    calc
      (1 : ℝ) < (256*K0^2/(36*M2^2*(4001/3999 : ℝ)))*(A^8*S^4) := hq1
      _ = K0^2*A^8*(2*B*S)^8/(36*M2^2*B^8*S^4*(4001/3999 : ℝ)) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ K0^2*A^8*T^8/(36*M2^2*B^8*S^4*(4001/3999 : ℝ)) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | positivity
      _ = A^4*(K0*A^2*T^5/S^2)^2/(36*M2^2*B^8*T^2*(4001/3999 : ℝ)) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ A^4*C^2/(36*M2^2*B^8*T^2*(4001/3999 : ℝ)) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | positivity
  have hr2 : 1 < A^6*C^2/((16*R2^2*2400^2*(4001/3999 : ℝ))*B^6*S^6) := by
    calc
      (1 : ℝ) < (G^2/(16*R2^2*2400^2*(4001/3999 : ℝ)))*(A^20*B^4) := hq2
      _ = A^6*(G*(A^7*B^5*S^3))^2/((16*R2^2*2400^2*(4001/3999 : ℝ))*B^6*S^6) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ A^6*C^2/((16*R2^2*2400^2*(4001/3999 : ℝ))*B^6*S^6) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | positivity
  have hr3 : 1 < A^6*C^2/((16*R2^2*2400^2*(4001/3999 : ℝ))*B^10*S^4) := by
    calc
      (1 : ℝ) < (G^2/(16*R2^2*2400^2*(4001/3999 : ℝ)))*(A^20*S^2) := hq3
      _ = A^6*(G*(A^7*B^5*S^3))^2/((16*R2^2*2400^2*(4001/3999 : ℝ))*B^10*S^4) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ A^6*C^2/((16*R2^2*2400^2*(4001/3999 : ℝ))*B^10*S^4) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | positivity
  have hr4 (hextra : B^2 ≤ S) : 1 < A^6*C^2/((16*Rp^2*Mn^2*(4001/3999 : ℝ))*B^14*S^4) := by
    calc
      (1 : ℝ) < (G^2/(16*Rp^2*Mn^2*(4001/3999 : ℝ)))*(A^20) := hq4
      _ = G^2*A^20*(B^2)^2/((16*Rp^2*Mn^2*(4001/3999 : ℝ))*B^4) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ G^2*A^20*S^2/((16*Rp^2*Mn^2*(4001/3999 : ℝ))*B^4) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | exact hextra | positivity
      _ = A^6*(G*(A^7*B^5*S^3))^2/((16*Rp^2*Mn^2*(4001/3999 : ℝ))*B^14*S^4) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ A^6*C^2/((16*Rp^2*Mn^2*(4001/3999 : ℝ))*B^14*S^4) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | exact hextra | positivity
  have hr5 : 1 < A^6*C^2/((16*Rp^2*M3^2*(4001/3999 : ℝ))*B^12*S^4) := by
    calc
      (1 : ℝ) < (G^2/(16*Rp^2*M3^2*(4001/3999 : ℝ)))*(A^20) := hq5
      _ = G^2*A^20*B^2/((16*Rp^2*M3^2*(4001/3999 : ℝ))*B^2) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ G^2*A^20*S^2/((16*Rp^2*M3^2*(4001/3999 : ℝ))*B^2) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | positivity
      _ = A^6*(G*(A^7*B^5*S^3))^2/((16*Rp^2*M3^2*(4001/3999 : ℝ))*B^12*S^4) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ A^6*C^2/((16*Rp^2*M3^2*(4001/3999 : ℝ))*B^12*S^4) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | positivity
  have hr6 (hextra : S ≤ B^2) : 1 < A^8*C^4/((16*R3^2*((8/9 : ℝ)*608^2)^2*(4001/3999 : ℝ))*B^12*S^16) := by
    calc
      (1 : ℝ) < (G^4/(16*R3^2*((8/9 : ℝ)*608^2)^2*(4001/3999 : ℝ)))*(A^36) := hq6
      _ = G^4*A^36*S^4/((16*R3^2*((8/9 : ℝ)*608^2)^2*(4001/3999 : ℝ))*S^4) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ G^4*A^36*(B^2)^4/((16*R3^2*((8/9 : ℝ)*608^2)^2*(4001/3999 : ℝ))*S^4) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | exact hextra | positivity
      _ = A^8*(G*(A^7*B^5*S^3))^4/((16*R3^2*((8/9 : ℝ)*608^2)^2*(4001/3999 : ℝ))*B^12*S^16) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ A^8*C^4/((16*R3^2*((8/9 : ℝ)*608^2)^2*(4001/3999 : ℝ))*B^12*S^16) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | exact hextra | positivity
  have hr7 : 1 < A^6*C^4/((16*(3920/81 : ℝ)^2*Mn^2*(4001/3999 : ℝ))*B^18*S^10) := by
    calc
      (1 : ℝ) < (G^4/(16*(3920/81 : ℝ)^2*Mn^2*(4001/3999 : ℝ)))*(A^34*B^2*S^2) := hq7
      _ = A^6*(G*(A^7*B^5*S^3))^4/((16*(3920/81 : ℝ)^2*Mn^2*(4001/3999 : ℝ))*B^18*S^10) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ A^6*C^4/((16*(3920/81 : ℝ)^2*Mn^2*(4001/3999 : ℝ))*B^18*S^10) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | positivity
  have hr8 (hextra : B^3 ≤ S) : 1 < A^8*C^2/((16*Rn^2*M4^2*(4001/3999 : ℝ))*B^24) := by
    calc
      (1 : ℝ) < (G^2/(16*Rn^2*M4^2*(4001/3999 : ℝ)))*(A^22*B^4) := hq8
      _ = G^2*A^22*(B^3)^6/((16*Rn^2*M4^2*(4001/3999 : ℝ))*B^14) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ G^2*A^22*S^6/((16*Rn^2*M4^2*(4001/3999 : ℝ))*B^14) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | exact hextra | positivity
      _ = A^8*(G*(A^7*B^5*S^3))^2/((16*Rn^2*M4^2*(4001/3999 : ℝ))*B^24) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ A^8*C^2/((16*Rn^2*M4^2*(4001/3999 : ℝ))*B^24) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | exact hextra | positivity
  have hr9 (hextra : S ≤ B^3) : 1 < A^8*C^4/((16*Rn^2*Mbs^2*(4001/3999 : ℝ))*B^6*S^14) := by
    calc
      (1 : ℝ) < (G^4/(16*Rn^2*Mbs^2*(4001/3999 : ℝ)))*(A^36*B^8) := hq9
      _ = G^4*A^36*B^8*S^2/((16*Rn^2*Mbs^2*(4001/3999 : ℝ))*S^2) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ G^4*A^36*B^8*(B^3)^2/((16*Rn^2*Mbs^2*(4001/3999 : ℝ))*S^2) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | exact hextra | positivity
      _ = A^8*(G*(A^7*B^5*S^3))^4/((16*Rn^2*Mbs^2*(4001/3999 : ℝ))*B^6*S^14) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ A^8*C^4/((16*Rn^2*Mbs^2*(4001/3999 : ℝ))*B^6*S^14) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | exact hextra | positivity
  have hr10 : 1 < 1*C^2/((16*Rbs^2*M4^2*(4001/3999 : ℝ))*B^10*S^6) := by
    calc
      (1 : ℝ) < (rho^2/(16*M4^2*(4001/3999 : ℝ)))*A^14 := hq10
      _ = 1*((rho*Rbs)*(A^7*B^5*S^3))^2/((16*Rbs^2*M4^2*(4001/3999 : ℝ))*B^10*S^6) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ 1*C^2/((16*Rbs^2*M4^2*(4001/3999 : ℝ))*B^10*S^6) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | positivity
  have hr11 : 1 < A^10*C^4/((144*R4^2*42^8*(4001/3999 : ℝ))*B^30) := by
    calc
      (1 : ℝ) < (G^4/(144*R4^2*42^8*(4001/3999 : ℝ)))*(A^38*B^2) := hq11
      _ = G^4*A^38*B^12/((144*R4^2*42^8*(4001/3999 : ℝ))*B^10) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ G^4*A^38*S^12/((144*R4^2*42^8*(4001/3999 : ℝ))*B^10) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | positivity
      _ = A^10*(G*(A^7*B^5*S^3))^4/((144*R4^2*42^8*(4001/3999 : ℝ))*B^30) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ A^10*C^4/((144*R4^2*42^8*(4001/3999 : ℝ))*B^30) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | positivity
  have hr12 : 1 < A^8*C^4/((4*M5^2*(5/2 : ℝ)^8*(4001/3999 : ℝ))*B^32) := by
    calc
      (1 : ℝ) < (G^4/(4*M5^2*(5/2 : ℝ)^8*(4001/3999 : ℝ)))*(A^36) := hq12
      _ = G^4*A^36*B^12/((4*M5^2*(5/2 : ℝ)^8*(4001/3999 : ℝ))*B^12) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ G^4*A^36*S^12/((4*M5^2*(5/2 : ℝ)^8*(4001/3999 : ℝ))*B^12) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | positivity
      _ = A^8*(G*(A^7*B^5*S^3))^4/((4*M5^2*(5/2 : ℝ)^8*(4001/3999 : ℝ))*B^32) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ A^8*C^4/((4*M5^2*(5/2 : ℝ)^8*(4001/3999 : ℝ))*B^32) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | positivity
  have hr13 : 1 < A^12*C^6/((144*R5^2*42^10*(4001/3999 : ℝ))*B^38) := by
    calc
      (1 : ℝ) < (G^6/(144*R5^2*42^10*(4001/3999 : ℝ)))*(A^54*B^10) := hq13
      _ = G^6*A^54*B^18/((144*R5^2*42^10*(4001/3999 : ℝ))*B^8) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ G^6*A^54*S^18/((144*R5^2*42^10*(4001/3999 : ℝ))*B^8) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | positivity
      _ = A^12*(G*(A^7*B^5*S^3))^6/((144*R5^2*42^10*(4001/3999 : ℝ))*B^38) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ A^12*C^6/((144*R5^2*42^10*(4001/3999 : ℝ))*B^38) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | positivity
  have hr14 : 1 < A^10*C^6/((36*42^12*(5/2 : ℝ)^10*(4001/3999 : ℝ))*B^44) := by
    calc
      (1 : ℝ) < (G^6/(36*42^12*(5/2 : ℝ)^10*(4001/3999 : ℝ)))*(A^52*B^4) := hq14
      _ = G^6*A^52*B^18/((36*42^12*(5/2 : ℝ)^10*(4001/3999 : ℝ))*B^14) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ G^6*A^52*S^18/((36*42^12*(5/2 : ℝ)^10*(4001/3999 : ℝ))*B^14) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | positivity
      _ = A^10*(G*(A^7*B^5*S^3))^6/((36*42^12*(5/2 : ℝ)^10*(4001/3999 : ℝ))*B^44) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ A^10*C^6/((36*42^12*(5/2 : ℝ)^10*(4001/3999 : ℝ))*B^44) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | positivity
  have hr15 : 1 < A*C^1/((105)*B^4) := by
    calc
      (1 : ℝ) < (G/(105))*(A^8*B*S^3) := hq15
      _ = A*(G*(A^7*B^5*S^3))^1/((105)*B^4) := by
        field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
        <;> ring
      _ ≤ A*C^1/((105)*B^4) := by
        gcongr <;> first | exact hC.le | exact hgap.le | exact hgapbs.le | exact hT.le | exact hBS | positivity
  have ho0 : (allLargeWindowQ A T C).1 < A^2*C^7/(S^2*T^4) := by
    apply window_overlap_of_ratio ((allLargeWindowQ A T C).1) (A^2*C^7/(S^2*T^4)) (A^2*C^4*(1-1/4000 : ℝ)/(12100*S^2*T^10))
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
      <;> ring
    · exact hr0
  have ho1 : (commonWindowN2 A B C M2 R2).1 < (allLargeWindowQ A T C).2 := by
    apply window_overlap_of_ratio ((commonWindowN2 A B C M2 R2).1) ((allLargeWindowQ A T C).2) (A^4*C^2/(36*M2^2*B^8*T^2*(4001/3999 : ℝ)))
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
      <;> ring
    · exact hr1
  have ho2 : 4*2400^2*(B*S^3)^2*C^5/(1-1/4000 : ℝ) < (commonWindowN2 A B C M2 R2).2 := by
    apply window_overlap_of_ratio (4*2400^2*(B*S^3)^2*C^5/(1-1/4000 : ℝ)) ((commonWindowN2 A B C M2 R2).2) (A^6*C^2/((16*R2^2*2400^2*(4001/3999 : ℝ))*B^6*S^6))
    · positivity
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
      <;> ring
    · exact hr2
  have ho3 : 4*2400^2*(B^3*S^2)^2*C^5/(1-1/4000 : ℝ) < (commonWindowN2 A B C M2 R2).2 := by
    apply window_overlap_of_ratio (4*2400^2*(B^3*S^2)^2*C^5/(1-1/4000 : ℝ)) ((commonWindowN2 A B C M2 R2).2) (A^6*C^2/((16*R2^2*2400^2*(4001/3999 : ℝ))*B^10*S^4))
    · positivity
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
      <;> ring
    · exact hr3
  have ho4 (hextra : B^2 ≤ S) : (commonWindowN3 A B C Mn Rn).1 < (commonWindowP A B S C Rp).2 := by
    apply window_overlap_of_ratio ((commonWindowN3 A B C Mn Rn).1) ((commonWindowP A B S C Rp).2) (A^6*C^2/((16*Rp^2*Mn^2*(4001/3999 : ℝ))*B^14*S^4))
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
      <;> ring
    · exact hr4 hextra
  have ho5 : (commonWindowA3 A B C M3 R3).1 < (commonWindowP A B S C Rp).2 := by
    apply window_overlap_of_ratio ((commonWindowA3 A B C M3 R3).1) ((commonWindowP A B S C Rp).2) (A^6*C^2/((16*Rp^2*M3^2*(4001/3999 : ℝ))*B^12*S^4))
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
      <;> ring
    · exact hr5
  have ho6 (hextra : S ≤ B^2) : (allLargeWindowM A B S C).1 < (commonWindowA3 A B C M3 R3).2 := by
    apply window_overlap_of_ratio ((allLargeWindowM A B S C).1) ((commonWindowA3 A B C M3 R3).2) (A^8*C^4/((16*R3^2*((8/9 : ℝ)*608^2)^2*(4001/3999 : ℝ))*B^12*S^16))
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
      <;> ring
    · exact hr6 hextra
  have ho7 : (commonWindowN3 A B C Mn Rn).1 < (allLargeWindowM A B S C).2 := by
    apply window_overlap_of_ratio ((commonWindowN3 A B C Mn Rn).1) ((allLargeWindowM A B S C).2) (A^6*C^4/((16*(3920/81 : ℝ)^2*Mn^2*(4001/3999 : ℝ))*B^18*S^10))
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
      <;> ring
    · exact hr7
  have ho8 (hextra : B^3 ≤ S) : (commonWindowA4 A B C M4 R4).1 < (commonWindowN3 A B C Mn Rn).2 := by
    apply window_overlap_of_ratio ((commonWindowA4 A B C M4 R4).1) ((commonWindowN3 A B C Mn Rn).2) (A^8*C^2/((16*Rn^2*M4^2*(4001/3999 : ℝ))*B^24))
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
      <;> ring
    · exact hr8 hextra
  have ho9 (hextra : S ≤ B^3) : (commonWindowN3 B S C Mbs Rbs).1 < (commonWindowN3 A B C Mn Rn).2 := by
    apply window_overlap_of_ratio ((commonWindowN3 B S C Mbs Rbs).1) ((commonWindowN3 A B C Mn Rn).2) (A^8*C^4/((16*Rn^2*Mbs^2*(4001/3999 : ℝ))*B^6*S^14))
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
      <;> ring
    · exact hr9 hextra
  have ho10 : (commonWindowA4 A B C M4 R4).1 < (commonWindowN3 B S C Mbs Rbs).2 := by
    apply window_overlap_of_ratio ((commonWindowA4 A B C M4 R4).1) ((commonWindowN3 B S C Mbs Rbs).2) (1*C^2/((16*Rbs^2*M4^2*(4001/3999 : ℝ))*B^10*S^6))
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
      <;> ring
    · exact hr10
  have ho11 : ordinaryWindowLower B C 4 < (commonWindowA4 A B C M4 R4).2 := by
    apply window_overlap_of_ratio (ordinaryWindowLower B C 4) ((commonWindowA4 A B C M4 R4).2) (A^10*C^4/((144*R4^2*42^8*(4001/3999 : ℝ))*B^30))
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
      <;> ring
    · exact hr11
  have ho12 : (commonWindowA5 A B C M5 R5).1 < ordinaryWindowUpper A B C 4 := by
    apply window_overlap_of_ratio ((commonWindowA5 A B C M5 R5).1) (ordinaryWindowUpper A B C 4) (A^8*C^4/((4*M5^2*(5/2 : ℝ)^8*(4001/3999 : ℝ))*B^32))
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
      <;> ring
    · exact hr12
  have ho13 : ordinaryWindowLower B C 5 < (commonWindowA5 A B C M5 R5).2 := by
    apply window_overlap_of_ratio (ordinaryWindowLower B C 5) ((commonWindowA5 A B C M5 R5).2) (A^12*C^6/((144*R5^2*42^10*(4001/3999 : ℝ))*B^38))
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
      <;> ring
    · exact hr13
  have ho14 : ordinaryWindowLower B C 6 < ordinaryWindowUpper A B C 5 := by
    apply window_overlap_of_ratio (ordinaryWindowLower B C 6) (ordinaryWindowUpper A B C 5) (A^10*C^6/((36*42^12*(5/2 : ℝ)^10*(4001/3999 : ℝ))*B^44))
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      positivity
    · dsimp [allLargeWindowQ,allLargeWindowM,commonWindowN2,commonWindowN3,commonWindowP,commonWindowA3,commonWindowA4,commonWindowA5,ordinaryWindowLower,ordinaryWindowUpper]
      field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
      <;> ring
    · exact hr14
  have ho15 : 42*B^3*C < 2*A*C^2/(5*B) := by
    apply window_overlap_of_ratio (42*B^3*C) (2*A*C^2/(5*B)) (A*C^1/((105)*B^4))
    · positivity
    · field_simp [hA0.ne',hB0.ne',hS0.ne',hT0.ne',hC0.ne',hG.ne',hrho.ne',hK0.ne',hM2.ne',hMn.ne',hM3.ne',hM4.ne',hM5.ne',hMbs.ne',hR2.ne',hRn.ne',hR3.ne',hR4.ne',hR5.ne',hRbs.ne',hRp.ne']
      <;> ring
    · exact hr15
  have hoP : (commonWindowP A B S C Rp).1 < (commonWindowN2 A B C M2 R2).2 := by
    rcases le_total (B*S^3) (B^3*S^2) with h | h
    · simpa only [commonWindowP,max_eq_right h] using ho3
    · simpa only [commonWindowP,max_eq_left h] using ho2
  exact ⟨ho0,ho1,hoP,ho4,ho5,ho6,ho7,ho8,ho9,ho10,ho11,ho12,ho13,ho14,ho15⟩

end D1Bound5
end
