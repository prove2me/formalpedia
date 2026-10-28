-- Prove2me | solution 1 for D1Bound5.fixed_cutoff_window_overlaps
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:20:26.381054+00:00
-- url     : https://prove2.me/submissions/669d7a2f-8e25-4728-86ea-93e8b023ccb4

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
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_AllLargeWindows_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallFixedWindows_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_OrdinaryClosedIntervals_Definitions
import Theorems.Thm_D1Bound5_OneSmallCutoffRow_overlaps_at_real
import Theorems.Thm_D1Bound5_oneSmallCutoffRows_residuals_pos
import Theorems.Thm_D1Bound5_oneSmallCutoffRows_valid
import Theorems.Thm_D1Bound5_window_overlap_of_ratio

section
namespace D1Bound5











/-- Every adjacent fixed-table window overlaps for all fourth moduli at
or beyond its certified cutoff. The actual analytic exclusions are supplied
separately when this scalar theorem is applied to a tuple. -/
theorem _root_.solution (r : OneSmallCutoffRow) (hr : r ∈ oneSmallCutoffRows)
    (B S T C : ℝ) (hB : 0 < B) (hS : 0 < S) (hT : 0 < T)
    (hBsq : B^2 = (r.b0 : ℝ)) (hSsq : S^2 = (r.s0 : ℝ))
    (hlarge : (r.triple.cutoff : ℝ) ≤ T^2)
    (hgap : (r.retainedCoefficient : ℝ)*T^5/S^2 < C) :
    (fixedWindowN2 r B C).1 < (allLargeWindowQ 1 T C).2 ∧
    (fixedWindowP r B S C).1 < (fixedWindowN2 r B C).2 ∧
    (fixedWindowA3 r B C).1 < (fixedWindowP r B S C).2 ∧
    (allLargeWindowM 1 B S C).1 < (fixedWindowA3 r B C).2 ∧
    (fixedWindowN3 r B C).1 < (allLargeWindowM 1 B S C).2 ∧
    (fixedWindowN3bs r B S C).1 < (fixedWindowN3 r B C).2 ∧
    (fixedWindowA4 r B C).1 < (fixedWindowN3bs r B S C).2 ∧
    ordinaryWindowLower B C 4 < (fixedWindowA4 r B C).2 ∧
    (fixedWindowA5 r B C).1 < ordinaryWindowUpper 1 B C 4 ∧
    ordinaryWindowLower B C 5 < (fixedWindowA5 r B C).2 ∧
    ordinaryWindowLower B C 6 < ordinaryWindowUpper 1 B C 5 ∧
    42*B^3*C < 2*C^2/(5*B) := by
  have hv := oneSmallCutoffRows_valid r hr
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hK,hM2,hMn,hM3,hM4,hM5,hMbs,_,htail⟩ :=
    oneSmallCutoffRows_valid r hr
  obtain ⟨hR2,hRn,hR3,hR4,hR5,hRbs,hRp⟩ := oneSmallCutoffRows_residuals_pos r hr
  have hKpos : 0 < (r.retainedCoefficient : ℝ) := by exact_mod_cast (show (0 : ℚ) < r.retainedCoefficient from lt_trans (by norm_num) hK)
  have hM2pos : 0 < (r.M2 : ℝ) := by exact_mod_cast hM2
  have hMnpos : 0 < (r.Mn : ℝ) := by exact_mod_cast hMn
  have hM3pos : 0 < (r.M3 : ℝ) := by exact_mod_cast hM3
  have hM4pos : 0 < (r.M4 : ℝ) := by exact_mod_cast hM4
  have hM5pos : 0 < (r.M5 : ℝ) := by exact_mod_cast hM5
  have hMbspos : 0 < (r.Mbs : ℝ) := by exact_mod_cast hMbs
  have hR2pos : 0 < (r.R2 : ℝ) := by exact_mod_cast hR2
  have hRnpos : 0 < (r.Rn : ℝ) := by exact_mod_cast hRn
  have hR3pos : 0 < (r.R3 : ℝ) := by exact_mod_cast hR3
  have hR4pos : 0 < (r.R4 : ℝ) := by exact_mod_cast hR4
  have hR5pos : 0 < (r.R5 : ℝ) := by exact_mod_cast hR5
  have hRbspos : 0 < (r.Rbs : ℝ) := by exact_mod_cast hRbs
  have hRppos : 0 < (r.Rp : ℝ) := by exact_mod_cast hRp
  have hC : 0 < C := (by positivity : 0 < (r.retainedCoefficient : ℝ)*T^5/S^2).trans hgap
  have hr1 : 1 < C^2/(36*(r.M2 : ℝ)^2*B^8*T^2*(4001/3999 : ℝ)) := by
    have hh := r.overlaps_at_real hv (T^2) hlarge
      ((r.retainedCoefficient^2/(36*r.M2^2*r.b0^4*r.s0^2*(4001/3999)) : ℚ),4) (by simp [OneSmallCutoffRow.overlaps])
    have hbase : 1 < ((r.retainedCoefficient : ℝ)*T^5/S^2)^2/(36*(r.M2 : ℝ)^2*B^8*T^2*(4001/3999 : ℝ)) := by
      push_cast at hh
      rw [←hBsq,←hSsq] at hh
      convert hh using 1 <;> field_simp [hB.ne',hS.ne',hT.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne'] <;> ring
    apply hbase.trans_le
    gcongr <;> first | exact hgap.le | positivity
  have hr2 : 1 < C^2/(16*(r.R2 : ℝ)^2*2400^2*B^6*S^6*(4001/3999 : ℝ)) := by
    have hh := r.overlaps_at_real hv (T^2) hlarge
      ((r.retainedCoefficient^2/(16*r.R2^2*2400^2*r.b0^3*r.s0^5*(4001/3999)) : ℚ),5) (by simp [OneSmallCutoffRow.overlaps])
    have hbase : 1 < ((r.retainedCoefficient : ℝ)*T^5/S^2)^2/(16*(r.R2 : ℝ)^2*2400^2*B^6*S^6*(4001/3999 : ℝ)) := by
      push_cast at hh
      rw [←hBsq,←hSsq] at hh
      convert hh using 1 <;> field_simp [hB.ne',hS.ne',hT.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne'] <;> ring
    apply hbase.trans_le
    gcongr <;> first | exact hgap.le | positivity
  have hr3 : 1 < C^2/(16*(r.R2 : ℝ)^2*2400^2*B^10*S^4*(4001/3999 : ℝ)) := by
    have hh := r.overlaps_at_real hv (T^2) hlarge
      ((r.retainedCoefficient^2/(16*r.R2^2*2400^2*r.b0^5*r.s0^4*(4001/3999)) : ℚ),5) (by simp [OneSmallCutoffRow.overlaps])
    have hbase : 1 < ((r.retainedCoefficient : ℝ)*T^5/S^2)^2/(16*(r.R2 : ℝ)^2*2400^2*B^10*S^4*(4001/3999 : ℝ)) := by
      push_cast at hh
      rw [←hBsq,←hSsq] at hh
      convert hh using 1 <;> field_simp [hB.ne',hS.ne',hT.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne'] <;> ring
    apply hbase.trans_le
    gcongr <;> first | exact hgap.le | positivity
  have hr4 : 1 < C^2/(16*(r.Rp : ℝ)^2*(r.M3 : ℝ)^2*B^12*S^4*(4001/3999 : ℝ)) := by
    have hh := r.overlaps_at_real hv (T^2) hlarge
      ((r.retainedCoefficient^2/(16*r.Rp^2*r.M3^2*r.b0^6*r.s0^4*(4001/3999)) : ℚ),5) (by simp [OneSmallCutoffRow.overlaps])
    have hbase : 1 < ((r.retainedCoefficient : ℝ)*T^5/S^2)^2/(16*(r.Rp : ℝ)^2*(r.M3 : ℝ)^2*B^12*S^4*(4001/3999 : ℝ)) := by
      push_cast at hh
      rw [←hBsq,←hSsq] at hh
      convert hh using 1 <;> field_simp [hB.ne',hS.ne',hT.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne'] <;> ring
    apply hbase.trans_le
    gcongr <;> first | exact hgap.le | positivity
  have hr5 : 1 < C^4/(16*(r.R3 : ℝ)^2*((8/9 : ℝ)*608^2)^2*B^12*S^16*(4001/3999 : ℝ)) := by
    have hh := r.overlaps_at_real hv (T^2) hlarge
      ((r.retainedCoefficient^4/(16*r.R3^2*((8/9)*608^2)^2*r.b0^6*r.s0^12*(4001/3999)) : ℚ),10) (by simp [OneSmallCutoffRow.overlaps])
    have hbase : 1 < ((r.retainedCoefficient : ℝ)*T^5/S^2)^4/(16*(r.R3 : ℝ)^2*((8/9 : ℝ)*608^2)^2*B^12*S^16*(4001/3999 : ℝ)) := by
      push_cast at hh
      rw [←hBsq,←hSsq] at hh
      convert hh using 1 <;> field_simp [hB.ne',hS.ne',hT.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne'] <;> ring
    apply hbase.trans_le
    gcongr <;> first | exact hgap.le | positivity
  have hr6 : 1 < C^4/(16*(3920/81 : ℝ)^2*(r.Mn : ℝ)^2*B^18*S^10*(4001/3999 : ℝ)) := by
    have hh := r.overlaps_at_real hv (T^2) hlarge
      ((r.retainedCoefficient^4/(16*(3920/81)^2*r.Mn^2*r.b0^9*r.s0^9*(4001/3999)) : ℚ),10) (by simp [OneSmallCutoffRow.overlaps])
    have hbase : 1 < ((r.retainedCoefficient : ℝ)*T^5/S^2)^4/(16*(3920/81 : ℝ)^2*(r.Mn : ℝ)^2*B^18*S^10*(4001/3999 : ℝ)) := by
      push_cast at hh
      rw [←hBsq,←hSsq] at hh
      convert hh using 1 <;> field_simp [hB.ne',hS.ne',hT.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne'] <;> ring
    apply hbase.trans_le
    gcongr <;> first | exact hgap.le | positivity
  have hr7 : 1 < C^4/(16*(r.Rn : ℝ)^2*(r.Mbs : ℝ)^2*B^6*S^14*(4001/3999 : ℝ)) := by
    have hh := r.overlaps_at_real hv (T^2) hlarge
      ((r.retainedCoefficient^4/(16*r.Rn^2*r.Mbs^2*r.b0^3*r.s0^11*(4001/3999)) : ℚ),10) (by simp [OneSmallCutoffRow.overlaps])
    have hbase : 1 < ((r.retainedCoefficient : ℝ)*T^5/S^2)^4/(16*(r.Rn : ℝ)^2*(r.Mbs : ℝ)^2*B^6*S^14*(4001/3999 : ℝ)) := by
      push_cast at hh
      rw [←hBsq,←hSsq] at hh
      convert hh using 1 <;> field_simp [hB.ne',hS.ne',hT.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne'] <;> ring
    apply hbase.trans_le
    gcongr <;> first | exact hgap.le | positivity
  have hr8 : 1 < C^2/(16*(r.Rbs : ℝ)^2*(r.M4 : ℝ)^2*B^10*S^6*(4001/3999 : ℝ)) := by
    have hh := r.overlaps_at_real hv (T^2) hlarge
      ((r.retainedCoefficient^2/(16*r.Rbs^2*r.M4^2*r.b0^5*r.s0^5*(4001/3999)) : ℚ),5) (by simp [OneSmallCutoffRow.overlaps])
    have hbase : 1 < ((r.retainedCoefficient : ℝ)*T^5/S^2)^2/(16*(r.Rbs : ℝ)^2*(r.M4 : ℝ)^2*B^10*S^6*(4001/3999 : ℝ)) := by
      push_cast at hh
      rw [←hBsq,←hSsq] at hh
      convert hh using 1 <;> field_simp [hB.ne',hS.ne',hT.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne'] <;> ring
    apply hbase.trans_le
    gcongr <;> first | exact hgap.le | positivity
  have hr9 : 1 < C^4/(144*(r.R4 : ℝ)^2*42^8*B^30*(4001/3999 : ℝ)) := by
    have hh := r.overlaps_at_real hv (T^2) hlarge
      ((r.retainedCoefficient^4/(144*r.R4^2*42^8*r.b0^15*r.s0^4*(4001/3999)) : ℚ),10) (by simp [OneSmallCutoffRow.overlaps])
    have hbase : 1 < ((r.retainedCoefficient : ℝ)*T^5/S^2)^4/(144*(r.R4 : ℝ)^2*42^8*B^30*(4001/3999 : ℝ)) := by
      push_cast at hh
      rw [←hBsq,←hSsq] at hh
      convert hh using 1 <;> field_simp [hB.ne',hS.ne',hT.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne'] <;> ring
    apply hbase.trans_le
    gcongr <;> first | exact hgap.le | positivity
  have hr10 : 1 < (2/5 : ℝ)^8*C^4/(4*(r.M5 : ℝ)^2*B^32*(4001/3999 : ℝ)) := by
    have hh := r.overlaps_at_real hv (T^2) hlarge
      (((2/5)^8*r.retainedCoefficient^4/(4*r.M5^2*r.b0^16*r.s0^4*(4001/3999)) : ℚ),10) (by simp [OneSmallCutoffRow.overlaps])
    have hbase : 1 < (2/5 : ℝ)^8*((r.retainedCoefficient : ℝ)*T^5/S^2)^4/(4*(r.M5 : ℝ)^2*B^32*(4001/3999 : ℝ)) := by
      push_cast at hh
      rw [←hBsq,←hSsq] at hh
      convert hh using 1 <;> field_simp [hB.ne',hS.ne',hT.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne'] <;> ring
    apply hbase.trans_le
    gcongr <;> first | exact hgap.le | positivity
  have hr11 : 1 < C^6/(144*(r.R5 : ℝ)^2*42^10*B^38*(4001/3999 : ℝ)) := by
    have hh := r.overlaps_at_real hv (T^2) hlarge
      ((r.retainedCoefficient^6/(144*r.R5^2*42^10*r.b0^19*r.s0^6*(4001/3999)) : ℚ),15) (by simp [OneSmallCutoffRow.overlaps])
    have hbase : 1 < ((r.retainedCoefficient : ℝ)*T^5/S^2)^6/(144*(r.R5 : ℝ)^2*42^10*B^38*(4001/3999 : ℝ)) := by
      push_cast at hh
      rw [←hBsq,←hSsq] at hh
      convert hh using 1 <;> field_simp [hB.ne',hS.ne',hT.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne'] <;> ring
    apply hbase.trans_le
    gcongr <;> first | exact hgap.le | positivity
  have hr12 : 1 < (2/5 : ℝ)^10*C^6/(36*42^12*B^44*(4001/3999 : ℝ)) := by
    have hh := r.overlaps_at_real hv (T^2) hlarge
      (((2/5)^10*r.retainedCoefficient^6/(36*42^12*r.b0^22*r.s0^6*(4001/3999)) : ℚ),15) (by simp [OneSmallCutoffRow.overlaps])
    have hbase : 1 < (2/5 : ℝ)^10*((r.retainedCoefficient : ℝ)*T^5/S^2)^6/(36*42^12*B^44*(4001/3999 : ℝ)) := by
      push_cast at hh
      rw [←hBsq,←hSsq] at hh
      convert hh using 1 <;> field_simp [hB.ne',hS.ne',hT.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne'] <;> ring
    apply hbase.trans_le
    gcongr <;> first | exact hgap.le | positivity
  have hrate : 42*B^3*C < 2*C^2/(5*B) := by
    have hn : 0 < (r.triple.cutoff : ℝ) := by
      have hh : (1024 : ℝ) ≤ r.triple.cutoff := by exact_mod_cast hv.1
      linarith only [hh]
    change 1 < r.retainedCoefficient^2*(r.triple.cutoff : ℚ)^5/(105^2*r.b0^4*r.s0^2) at htail
    have hs : 1 < (r.retainedCoefficient : ℝ)^2*(r.triple.cutoff : ℝ)^5/
        (105^2*(r.b0 : ℝ)^4*(r.s0 : ℝ)^2) := by
      exact_mod_cast htail
    rw [←hBsq,←hSsq] at hs
    have hp : (r.triple.cutoff : ℝ)^5 ≤ (T^2)^5 := by gcongr
    have hs' : 1 < (r.retainedCoefficient : ℝ)^2*T^10/(105^2*B^8*S^4) := by
      calc
        (1 : ℝ) < (r.retainedCoefficient : ℝ)^2*(r.triple.cutoff : ℝ)^5/
            (105^2*(B^2)^4*(S^2)^2) := hs
        _ ≤ (r.retainedCoefficient : ℝ)^2*(T^2)^5/(105^2*(B^2)^4*(S^2)^2) := by gcongr
        _ = _ := by ring
    have hs'' : (105*B^4*S^2)^2 < ((r.retainedCoefficient : ℝ)*T^5)^2 := by
      have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 105^2*B^8*S^4)).mp hs'
      nlinarith only [hh]
    have hlin : 105*B^4*S^2 < (r.retainedCoefficient : ℝ)*T^5 :=
      (sq_lt_sq₀ (by positivity) (by positivity)).mp hs''
    have hsmall : 105*B^4 < (r.retainedCoefficient : ℝ)*T^5/S^2 :=
      (lt_div_iff₀ (pow_pos hS 2)).mpr hlin
    have hc : 105*B^4 < C := hsmall.trans hgap
    apply (lt_div_iff₀ (by positivity : 0 < 5*B)).mpr
    have hm := mul_lt_mul_of_pos_right hc (by positivity : 0 < 2*C)
    nlinarith only [hm]
  have heq (l u q : ℝ) (hl : 0 < l) (h : u/l=q) (hq : 1 < q) : l<u :=
    window_overlap_of_ratio l u q hl h hq
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hrate⟩
  · apply heq _ _ _ (by simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]; positivity) _ hr1
    simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]
    field_simp [hB.ne',hS.ne',hT.ne',hC.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne']
    <;> ring
  · by_cases hm : B*S^3 ≤ B^3*S^2
    · apply heq _ _ _ (by simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]; positivity) _ hr3
      simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper,max_eq_right hm]
      field_simp [hB.ne',hS.ne',hT.ne',hC.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne']
      <;> ring
    · have hm' : B^3*S^2 ≤ B*S^3 := (le_of_not_ge hm)
      apply heq _ _ _ (by simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]; positivity) _ hr2
      simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper,max_eq_left hm']
      field_simp [hB.ne',hS.ne',hT.ne',hC.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne']
      <;> ring
  · apply heq _ _ _ (by simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]; positivity) _ hr4
    simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]
    field_simp [hB.ne',hS.ne',hT.ne',hC.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne']
    <;> ring
  · apply heq _ _ _ (by simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]; positivity) _ hr5
    simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]
    field_simp [hB.ne',hS.ne',hT.ne',hC.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne']
    <;> ring
  · apply heq _ _ _ (by simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]; positivity) _ hr6
    simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]
    field_simp [hB.ne',hS.ne',hT.ne',hC.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne']
    <;> ring
  · apply heq _ _ _ (by simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]; positivity) _ hr7
    simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]
    field_simp [hB.ne',hS.ne',hT.ne',hC.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne']
    <;> ring
  · apply heq _ _ _ (by simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]; positivity) _ hr8
    simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]
    field_simp [hB.ne',hS.ne',hT.ne',hC.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne']
    <;> ring
  · apply heq _ _ _ (by simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]; positivity) _ hr9
    simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]
    field_simp [hB.ne',hS.ne',hT.ne',hC.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne']
    <;> ring
  · apply heq _ _ _ (by simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]; positivity) _ hr10
    simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]
    simp only [show (2*4 : ℕ) = 8 by rfl]
    field_simp [hB.ne',hS.ne',hT.ne',hC.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne']
    <;> ring
  · apply heq _ _ _ (by simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]; positivity) _ hr11
    simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]
    field_simp [hB.ne',hS.ne',hT.ne',hC.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne']
    <;> ring
  · apply heq _ _ _ (by simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]; positivity) _ hr12
    simp only [fixedWindowN2,fixedWindowP,fixedWindowA3,fixedWindowN3,fixedWindowN3bs,fixedWindowA4,fixedWindowA5,allLargeWindowQ,allLargeWindowM,ordinaryWindowLower,ordinaryWindowUpper]
    simp only [show (2*5 : ℕ) = 10 by rfl]
    field_simp [hB.ne',hS.ne',hT.ne',hC.ne',hM2pos.ne',hMnpos.ne',hM3pos.ne',hM4pos.ne',hM5pos.ne',hMbspos.ne',hR2pos.ne',hRnpos.ne',hR3pos.ne',hR4pos.ne',hR5pos.ne',hRbspos.ne',hRppos.ne']
    <;> ring

end D1Bound5
end
