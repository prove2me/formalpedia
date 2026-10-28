-- Prove2me | solution 1 for D1Bound5.firstPairGeometry_common_overlap_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:30:10.151526+00:00
-- url     : https://prove2.me/submissions/ee2ef2f0-4beb-4f54-91b6-7165235ec02f

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
import Definitions.Def_D1Bound5_CommonIntervalWindows_Definitions
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_001

section
namespace D1Bound5

/-- The exact rational certificates give all shared real overlap
comparisons for every S≥15. Actual family estimates are separate. -/
theorem _root_.solution (r : FirstPairGeometryRow)
    (hr : r.Valid) (B S : ℝ) (hB : 0 < B)
    (hBn : B^2 = (r.b0 : ℝ)) (hS : 15 ≤ S) :
    CommonOverlapBounds 1 B S r.G r.rho (7/4)
      r.M2 r.Mn r.M3 r.M4 r.M5 4143 r.R2 r.Rn r.R3 r.R4 r.R5 r.Rp := by
  rcases hr with
    ⟨ha,hb,hd,hA1,hA1sq,hB0,hB0sq,hB1,hB1sq,hd1,hd1sq,hq,hQ,hm,hK,
      hG,hH,hF,hrho,hR2,hRn,hR3,hR4,hR5,hRp,hM2,hMn,hM3,hM4,hM5,hqs,htail⟩
  have hS0 : 0 < S := by linarith only [hS]
  have hpG : (0 : ℝ) < (r.G : ℝ) := by exact_mod_cast hG
  have hprho : (0 : ℝ) < (r.rho : ℝ) := by exact_mod_cast hrho
  have hpR2 : (0 : ℝ) < (r.R2 : ℝ) := by exact_mod_cast hR2
  have hpRn : (0 : ℝ) < (r.Rn : ℝ) := by exact_mod_cast hRn
  have hpR3 : (0 : ℝ) < (r.R3 : ℝ) := by exact_mod_cast hR3
  have hpR4 : (0 : ℝ) < (r.R4 : ℝ) := by exact_mod_cast hR4
  have hpR5 : (0 : ℝ) < (r.R5 : ℝ) := by exact_mod_cast hR5
  have hpRp : (0 : ℝ) < (r.Rp : ℝ) := by exact_mod_cast hRp
  have hpM2 : (0 : ℝ) < (r.M2 : ℝ) := by exact_mod_cast hM2
  have hpMn : (0 : ℝ) < (r.Mn : ℝ) := by exact_mod_cast hMn
  have hpM3 : (0 : ℝ) < (r.M3 : ℝ) := by exact_mod_cast hM3
  have hpM4 : (0 : ℝ) < (r.M4 : ℝ) := by exact_mod_cast hM4
  have hpM5 : (0 : ℝ) < (r.M5 : ℝ) := by exact_mod_cast hM5
  have hpB0 : (0 : ℝ) < (r.B0 : ℝ) := by exact_mod_cast hB0
  have hr0 : (1 : ℚ) < 9604*(1-1/4000)*r.b0^5/12100 := by
    exact lt_trans (by norm_num) (hqs _ (by simp [FirstPairGeometryRow.overlaps]))
  have hq0 : (1 : ℝ) < (1024*(7/4 : ℝ)^4*(1-1/4000 : ℝ)/12100)*(1^10*B^10) := by
    convert (show (1 : ℝ) < ((9604*(1-1/4000)*r.b0^5/12100 : ℚ) : ℝ) by exact_mod_cast hr0) using 1 <;>
      push_cast <;> try rw [← hBn]
    all_goals ring
  have hr1 : (1 : ℚ) < 784*225^2/(36*r.M2^2*(4001/3999)) := by
    exact lt_trans (by norm_num) (hqs _ (by simp [FirstPairGeometryRow.overlaps]))
  have hq1 : (1 : ℝ) < (256*(7/4 : ℝ)^2/(36*(r.M2 : ℝ)^2*(4001/3999 : ℝ)))*(1^8*(15 : ℝ)^4) := by
    convert (show (1 : ℝ) < ((784*225^2/(36*r.M2^2*(4001/3999)) : ℚ) : ℝ) by exact_mod_cast hr1) using 1 <;>
      push_cast <;> try rw [← hBn]
    all_goals ring
  have hr2 : (1 : ℚ) < r.G^2*r.b0^2/(16*r.R2^2*2400^2*(4001/3999)) := by
    exact lt_trans (by norm_num) (hqs _ (by simp [FirstPairGeometryRow.overlaps]))
  have hq2 : (1 : ℝ) < ((r.G : ℝ)^2/(16*(r.R2 : ℝ)^2*2400^2*(4001/3999 : ℝ)))*(1^20*B^4) := by
    convert (show (1 : ℝ) < ((r.G^2*r.b0^2/(16*r.R2^2*2400^2*(4001/3999)) : ℚ) : ℝ) by exact_mod_cast hr2) using 1 <;>
      push_cast <;> try rw [← hBn]
    all_goals ring
  have hr3 : (1 : ℚ) < r.G^2*225/(16*r.R2^2*2400^2*(4001/3999)) := by
    exact lt_trans (by norm_num) (hqs _ (by simp [FirstPairGeometryRow.overlaps]))
  have hq3 : (1 : ℝ) < ((r.G : ℝ)^2/(16*(r.R2 : ℝ)^2*2400^2*(4001/3999 : ℝ)))*(1^20*(15 : ℝ)^2) := by
    convert (show (1 : ℝ) < ((r.G^2*225/(16*r.R2^2*2400^2*(4001/3999)) : ℚ) : ℝ) by exact_mod_cast hr3) using 1 <;>
      push_cast <;> try rw [← hBn]
    all_goals ring
  have hr4 : (1 : ℚ) < r.G^2/(16*r.Rp^2*r.Mn^2*(4001/3999)) := by
    exact lt_trans (by norm_num) (hqs _ (by simp [FirstPairGeometryRow.overlaps]))
  have hq4 : (1 : ℝ) < ((r.G : ℝ)^2/(16*(r.Rp : ℝ)^2*(r.Mn : ℝ)^2*(4001/3999 : ℝ)))*(1^20) := by
    convert (show (1 : ℝ) < ((r.G^2/(16*r.Rp^2*r.Mn^2*(4001/3999)) : ℚ) : ℝ) by exact_mod_cast hr4) using 1 <;>
      push_cast <;> try rw [← hBn]
    all_goals ring
  have hr5 : (1 : ℚ) < r.G^2/(16*r.Rp^2*r.M3^2*(4001/3999)) := by
    exact lt_trans (by norm_num) (hqs _ (by simp [FirstPairGeometryRow.overlaps]))
  have hq5 : (1 : ℝ) < ((r.G : ℝ)^2/(16*(r.Rp : ℝ)^2*(r.M3 : ℝ)^2*(4001/3999 : ℝ)))*(1^20) := by
    convert (show (1 : ℝ) < ((r.G^2/(16*r.Rp^2*r.M3^2*(4001/3999)) : ℚ) : ℝ) by exact_mod_cast hr5) using 1 <;>
      push_cast <;> try rw [← hBn]
    all_goals ring
  have hr6 : (1 : ℚ) < r.G^4/(16*r.R3^2*((8/9)*608^2)^2*(4001/3999)) := by
    exact lt_trans (by norm_num) (hqs _ (by simp [FirstPairGeometryRow.overlaps]))
  have hq6 : (1 : ℝ) < ((r.G : ℝ)^4/(16*(r.R3 : ℝ)^2*((8/9 : ℝ)*608^2)^2*(4001/3999 : ℝ)))*(1^36) := by
    convert (show (1 : ℝ) < ((r.G^4/(16*r.R3^2*((8/9)*608^2)^2*(4001/3999)) : ℚ) : ℝ) by exact_mod_cast hr6) using 1 <;>
      push_cast <;> try rw [← hBn]
    all_goals ring
  have hr7 : (1 : ℚ) < r.G^4*r.b0*225/(16*(3920/81)^2*r.Mn^2*(4001/3999)) := by
    exact lt_trans (by norm_num) (hqs _ (by simp [FirstPairGeometryRow.overlaps]))
  have hq7 : (1 : ℝ) < ((r.G : ℝ)^4/(16*(3920/81 : ℝ)^2*(r.Mn : ℝ)^2*(4001/3999 : ℝ)))*(1^34*B^2*(15 : ℝ)^2) := by
    convert (show (1 : ℝ) < ((r.G^4*r.b0*225/(16*(3920/81)^2*r.Mn^2*(4001/3999)) : ℚ) : ℝ) by exact_mod_cast hr7) using 1 <;>
      push_cast <;> try rw [← hBn]
    all_goals ring
  have hr8 : (1 : ℚ) < r.G^2*r.b0^2/(16*r.Rn^2*r.M4^2*(4001/3999)) := by
    exact lt_trans (by norm_num) (hqs _ (by simp [FirstPairGeometryRow.overlaps]))
  have hq8 : (1 : ℝ) < ((r.G : ℝ)^2/(16*(r.Rn : ℝ)^2*(r.M4 : ℝ)^2*(4001/3999 : ℝ)))*(1^22*B^4) := by
    convert (show (1 : ℝ) < ((r.G^2*r.b0^2/(16*r.Rn^2*r.M4^2*(4001/3999)) : ℚ) : ℝ) by exact_mod_cast hr8) using 1 <;>
      push_cast <;> try rw [← hBn]
    all_goals ring
  have hr9 : (1 : ℚ) < r.G^4*r.b0^4/(16*r.Rn^2*4143^2*(4001/3999)) := by
    exact lt_trans (by norm_num) (hqs _ (by simp [FirstPairGeometryRow.overlaps]))
  have hq9 : (1 : ℝ) < ((r.G : ℝ)^4/(16*(r.Rn : ℝ)^2*4143^2*(4001/3999 : ℝ)))*(1^36*B^8) := by
    convert (show (1 : ℝ) < ((r.G^4*r.b0^4/(16*r.Rn^2*4143^2*(4001/3999)) : ℚ) : ℝ) by exact_mod_cast hr9) using 1 <;>
      push_cast <;> try rw [← hBn]
    all_goals ring
  have hr10 : (1 : ℚ) < r.rho^2/(16*r.M4^2*(4001/3999)) := by
    exact lt_trans (by norm_num) (hqs _ (by simp [FirstPairGeometryRow.overlaps]))
  have hq10 : (1 : ℝ) < ((r.rho : ℝ)^2/(16*(r.M4 : ℝ)^2*(4001/3999 : ℝ)))*1^14 := by
    convert (show (1 : ℝ) < ((r.rho^2/(16*r.M4^2*(4001/3999)) : ℚ) : ℝ) by exact_mod_cast hr10) using 1 <;>
      push_cast <;> try rw [← hBn]
    all_goals ring
  have hr11 : (1 : ℚ) < r.G^4*r.b0/(144*r.R4^2*42^8*(4001/3999)) := by
    exact lt_trans (by norm_num) (hqs _ (by simp [FirstPairGeometryRow.overlaps]))
  have hq11 : (1 : ℝ) < ((r.G : ℝ)^4/(144*(r.R4 : ℝ)^2*42^8*(4001/3999 : ℝ)))*(1^38*B^2) := by
    convert (show (1 : ℝ) < ((r.G^4*r.b0/(144*r.R4^2*42^8*(4001/3999)) : ℚ) : ℝ) by exact_mod_cast hr11) using 1 <;>
      push_cast <;> try rw [← hBn]
    all_goals ring
  have hr12 : (1 : ℚ) < r.G^4/(4*r.M5^2*(5/2)^8*(4001/3999)) := by
    exact lt_trans (by norm_num) (hqs _ (by simp [FirstPairGeometryRow.overlaps]))
  have hq12 : (1 : ℝ) < ((r.G : ℝ)^4/(4*(r.M5 : ℝ)^2*(5/2 : ℝ)^8*(4001/3999 : ℝ)))*(1^36) := by
    convert (show (1 : ℝ) < ((r.G^4/(4*r.M5^2*(5/2)^8*(4001/3999)) : ℚ) : ℝ) by exact_mod_cast hr12) using 1 <;>
      push_cast <;> try rw [← hBn]
    all_goals ring
  have hr13 : (1 : ℚ) < r.G^6*r.b0^5/(144*r.R5^2*42^10*(4001/3999)) := by
    exact lt_trans (by norm_num) (hqs _ (by simp [FirstPairGeometryRow.overlaps]))
  have hq13 : (1 : ℝ) < ((r.G : ℝ)^6/(144*(r.R5 : ℝ)^2*42^10*(4001/3999 : ℝ)))*(1^54*B^10) := by
    convert (show (1 : ℝ) < ((r.G^6*r.b0^5/(144*r.R5^2*42^10*(4001/3999)) : ℚ) : ℝ) by exact_mod_cast hr13) using 1 <;>
      push_cast <;> try rw [← hBn]
    all_goals ring
  have hr14 : (1 : ℚ) < r.G^6*r.b0^2/(36*42^12*(5/2)^10*(4001/3999)) := by
    exact lt_trans (by norm_num) (hqs _ (by simp [FirstPairGeometryRow.overlaps]))
  have hq14 : (1 : ℝ) < ((r.G : ℝ)^6/(36*42^12*(5/2 : ℝ)^10*(4001/3999 : ℝ)))*(1^52*B^4) := by
    convert (show (1 : ℝ) < ((r.G^6*r.b0^2/(36*42^12*(5/2)^10*(4001/3999)) : ℚ) : ℝ) by exact_mod_cast hr14) using 1 <;>
      push_cast <;> try rw [← hBn]
    all_goals ring
  have hB0B : (r.B0 : ℝ) ≤ B := by
    have hs : (r.B0 : ℝ)^2 ≤ B^2 := by
      rw [hBn]
      exact_mod_cast hB0sq
    nlinarith only [hs,hB,hpB0]
  have hqt : (1 : ℝ) < (r.G : ℝ)*(r.B0 : ℝ)*15^3/105 := by
    exact_mod_cast htail
  unfold CommonOverlapBounds
  refine ⟨hq0,?_,hq2,?_,hq4,hq5,hq6,?_,hq8,hq9,hq10,hq11,hq12,hq13,hq14,?_⟩
  · refine lt_of_lt_of_le hq1 ?_
    gcongr <;> first | exact hS | positivity
  · refine lt_of_lt_of_le hq3 ?_
    gcongr <;> first | exact hS | positivity
  · refine lt_of_lt_of_le hq7 ?_
    gcongr <;> first | exact hS | positivity
  · have hmono : (r.G : ℝ)*(r.B0 : ℝ)*15^3/105 ≤
        (r.G : ℝ)*B*S^3/105 := by
      gcongr <;> first | exact hB0B | exact hS | positivity
    simpa only [one_pow,one_mul,div_mul_eq_mul_div,mul_assoc] using
      lt_of_lt_of_le hqt hmono

end D1Bound5
end
