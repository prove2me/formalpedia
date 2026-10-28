-- Prove2me | solution 1 for D1Bound5.first_pair_retained_scalar
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:58:59.145977+00:00
-- url     : https://prove2.me/submissions/b712a0a3-0ff3-4cef-8381-e8cb7876b464

import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Monic
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
import Mathlib.Analysis.SpecificLimits.Normed
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
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_coherent_fixed_retained_coefficient_lower

section
namespace D1Bound5

/-- The retained interpolation coefficient and the coupled geometry
bound yield the three lower estimates used by the S≥15 window chain. -/
theorem _root_.solution (A B S T C R Q F Phi : ℝ)
    (hA : 1 ≤ A) (hB : 0 < B) (hS : 0 < S) (hT : 0 < T)
    (hR : 0 < R) (hRQ : R ≤ Q) (hF : 0 < F) (hPhi : 0 ≤ Phi)
    (hsep : (51051/400000 : ℝ)/B^2 < 1/Q)
    (hfront : (59/20 : ℝ)*A*B*S < T)
    (hgeom : R^2*Phi ≤ F)
    (hret : (9999/100 : ℝ)*A^2*
      (1/R-(51051/400000 : ℝ)/(A^2*B^2))^2*(T^5/S^2) < C) :
    let K := (9999/100 : ℝ)*A^2*(1/Q-(51051/400000 : ℝ)/B^2)^2
    let H := (9999/100 : ℝ)*A^2*(59/20 : ℝ)^5*
      (1-(51051/400000 : ℝ)*Q/B^2)^2
    K*T^5/S^2 < C ∧ K*(59/20 : ℝ)^5*B^5*S^3 < C ∧
      (H/F)*Phi*B^5*S^3 < C := by
  let e : ℝ := (51051/400000 : ℝ)/B^2
  let K : ℝ := (9999/100 : ℝ)*A^2*(1/Q-e)^2
  let KR : ℝ := (9999/100 : ℝ)*A^2*(1/R-e)^2
  let H : ℝ := (9999/100 : ℝ)*A^2*(59/20 : ℝ)^5*(1-e*Q)^2
  have hA0 : 0 < A := by linarith only [hA]
  have hQ : 0 < Q := hR.trans_le hRQ
  have he : 0 < e := by dsimp [e]; positivity
  have hsepR : e < 1/R := hsep.trans_le (one_div_le_one_div_of_le hR hRQ)
  have hdelQ : 0 < 1/Q-e := sub_pos.mpr hsep
  have hdelR : 0 < 1/R-e := sub_pos.mpr hsepR
  have hK : 0 < K := by dsimp [K]; positivity
  have hKR : 0 < KR := by dsimp [KR]; positivity
  have hKlower := coherent_fixed_retained_coefficient_lower A B R Q hA hB hR hRQ hsep
  have hKRlower := coherent_fixed_retained_coefficient_lower A B R R hA hB hR le_rfl hsepR
  have hKret : K*(T^5/S^2) < C :=
    (mul_le_mul_of_nonneg_right hKlower (by positivity : 0 ≤ T^5/S^2)).trans_lt hret
  have hKRret : KR*(T^5/S^2) < C :=
    (mul_le_mul_of_nonneg_right hKRlower (by positivity : 0 ≤ T^5/S^2)).trans_lt hret
  have hfront' : (59/20 : ℝ)*B*S < T := by
    have hh := mul_le_mul_of_nonneg_right hA (by positivity : 0 ≤ (59/20 : ℝ)*B*S)
    nlinarith only [hh,hfront]
  have hpower : (59/20 : ℝ)^5*B^5*S^3 < T^5/S^2 := by
    have hh : ((59/20 : ℝ)*B*S)^5 < T^5 := by gcongr
    apply (lt_div_iff₀ (pow_pos hS 2)).mpr
    calc
      (59/20 : ℝ)^5*B^5*S^3*S^2 = ((59/20 : ℝ)*B*S)^5 := by ring
      _ < T^5 := hh
  have hGrowth : K*(59/20 : ℝ)^5*B^5*S^3 < C := by
    have hh := (mul_lt_mul_of_pos_left hpower hK).trans hKret
    simpa only [mul_assoc] using hh
  have hGrowthR : KR*(59/20 : ℝ)^5*B^5*S^3 < C := by
    have hh := (mul_lt_mul_of_pos_left hpower hKR).trans hKRret
    simpa only [mul_assoc] using hh
  have hEQ : e*Q < 1 := by
    have hh := (lt_div_iff₀ hQ).mp hsep
    exact hh
  have hER : e*R ≤ e*Q := mul_le_mul_of_nonneg_left hRQ he.le
  have h1EQ : 0 < 1-e*Q := sub_pos.mpr hEQ
  have hHpos : 0 < H := by dsimp [H]; positivity
  have hsq : (1-e*Q)^2 ≤ (1-e*R)^2 := by
    apply (sq_le_sq₀ (by linarith only [hEQ]) (by linarith only [hEQ,hER])).mpr
    linarith only [hER]
  have hHbound : H/R^2 ≤ KR*(59/20 : ℝ)^5 := by
    calc
      H/R^2 ≤ ((9999/100 : ℝ)*A^2*(59/20 : ℝ)^5*(1-e*R)^2)/R^2 := by
        dsimp [H]
        gcongr
      _ = KR*(59/20 : ℝ)^5 := by
        dsimp [KR]
        field_simp [hR.ne']
        <;> ring
  have hPhiBound : Phi ≤ F/R^2 := (le_div_iff₀ (sq_pos_of_pos hR)).mpr (by nlinarith only [hgeom])
  have hCoupled : (H/F)*Phi ≤ KR*(59/20 : ℝ)^5 := by
    calc
      (H/F)*Phi ≤ (H/F)*(F/R^2) := mul_le_mul_of_nonneg_left hPhiBound (by positivity)
      _ = H/R^2 := by field_simp [hF.ne',hR.ne'] <;> ring
      _ ≤ _ := hHbound
  have hlast := (mul_le_mul_of_nonneg_right hCoupled (by positivity : 0 ≤ B^5*S^3)).trans_lt
    (by simpa only [mul_assoc] using hGrowthR)
  change K*T^5/S^2 < C ∧ K*(59/20 : ℝ)^5*B^5*S^3 < C ∧
    (((9999/100 : ℝ)*A^2*(59/20 : ℝ)^5*(1-(51051/400000 : ℝ)*Q/B^2)^2)/F)*Phi*B^5*S^3 < C
  refine ⟨by convert hKret using 1 <;> ring,hGrowth,?_⟩
  calc
    _ = (H/F)*Phi*(B^5*S^3) := by
      dsimp only [H,e]
      ring
    _ < C := hlast

end D1Bound5
end
