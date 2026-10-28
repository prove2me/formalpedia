-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.five_region_retained_gaps
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:41:27.128541+00:00
-- url     : https://prove2.me/submissions/df2bd21c-14b5-47b1-bfe4-795c80788b37

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
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
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
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
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoupledPhaseBounds_Definitions
import Definitions.Def_D1Bound5_CoupledPhaseGeometry_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions
import Definitions.Def_D1Bound5_FinitePAdaptiveResidual_Definitions
import Definitions.Def_D1Bound5_FiveRegionParameters_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Theorems.Thm_D1Bound5_IsD1Tuple_frontier_small_norm_growth
import Theorems.Thm_D1Bound5_IsD1Tuple_small_norm_retained_gap
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_coupled_phase_geometry
import Theorems.Thm_D1Bound5_coupled_phase_row_polynomial_bound
import Theorems.Thm_D1Bound5_fiveRegionAnchorRatio_nonneg
import Theorems.Thm_D1Bound5_fiveRegion_case_bounds
import Theorems.Thm_D1Bound5_fiveRegion_case_disjunction
import Theorems.Thm_D1Bound5_fiveRegion_parameters
import Theorems.Thm_D1Bound5_fiveRegion_retained_scalar
import Theorems.Thm_D1Bound5_one_le_norm_integer
import Theorems.Thm_D1Bound5_phaseVandermondeRatio_le_ratio_triangle

section
namespace D1Bound5














theorem coupled_phase_row_bound (a b s : ℂ) (q F : ℝ)
    (hrow : CoupledPhaseRow q F) (hB : 0 < ‖b‖) (hBS : ‖b‖ ≤ ‖s‖)
    (hsep : q*‖a‖ ≤ ‖b‖) :
    (phaseVandermondeRatio a b s)^2*phasePhi b s < F := by
  have hq : 1 ≤ q := by rcases hrow with h|h|h|h|h <;> rcases h with ⟨rfl,_⟩ <;> norm_num
  obtain ⟨x,hx,hx2,hbound⟩ := coupled_phase_geometry a b s q hq hB hBS hsep
  exact hbound.trans_lt (coupled_phase_row_polynomial_bound q F hrow x hx hx2)

end D1Bound5
end

section
open scoped NumberField
open Module

namespace D1Bound5





/-- The actual five-entry retained form and coupled complex phase give
both monomial gaps for each unbounded first-pair region. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 5 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (r : Fin 5) (hN8 : ‖phi (a 0 : K)‖^2 ≤ 8)
    (hcase : FiveRegionCase r ‖phi (a 0 : K)‖ ‖phi (a 1 : K)‖) :
    let A := ‖phi (a 0 : K)‖
    let B := ‖phi (a 1 : K)‖
    let S := ‖phi (a 2 : K)‖
    let C := ‖phi (a 4 : K)‖
    fiveRegionGap r*(A^7*B^5*S^3) < C ∧
      (fiveRegionCoupledGap r*((3535/409600 : ℝ)*phasePhi
        (phi (a 1 : K)) (phi (a 2 : K))))*(A^7*B^5*S^3) < C := by
  classical
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let A := ‖f (a 0)‖
  let B := ‖f (a 1)‖
  let S := ‖f (a 2)‖
  let T := ‖f (a 3)‖
  let C := ‖f (a 4)‖
  let R := phaseVandermondeRatio (f (a 0)) (f (a 1)) (f (a 2))
  have hA : 1 ≤ A := one_le_norm_integer hK phi (ha.2.1 0)
  have hAB : A ≤ B := hmon (by decide : (0 : Fin 5) ≤ 1)
  have hBS : B ≤ S := hmon (by decide : (1 : Fin 5) ≤ 2)
  have hc := fiveRegion_case_bounds r A B (norm_nonneg _) hN8 hcase
  have hB : 0 < B := by linarith only [hc.2.2.2.1]
  have hS : 0 < S := hB.trans_le hBS
  let i4 : Fin 4 → Fin 5 := ![0,1,2,3]
  have hi4 : Function.Injective i4 := by decide
  have hm4 : Monotone i4 := by decide
  have h4 : IsD1Tuple (fun j => a (i4 j)) :=
    ⟨ha.1.comp hi4,fun j => ha.2.1 (i4 j),fun j k hjk => ha.2.2 (i4 j) (i4 k) (hi4.ne hjk)⟩
  have hrows := IsD1Tuple.frontier_small_norm_growth hK phi (fun j => a (i4 j))
    h4 (hmon.comp hm4) hN8
  have hfront : fiveRegionFrontier r*A*B*S < T := by
    fin_cases r <;> norm_num [FiveRegionCase,fiveRegionMinNorm,fiveRegionMinB,-sq_eq_one_iff,
      (show (0 : Fin 5) ≠ 4 by decide)] at hcase
    · exact hrows.1 hcase.1 hcase.2
    · exact hrows.2.1 hcase.1 hcase.2
    · exact hrows.2.2.1 hcase.1 hcase.2
    · exact hrows.2.2.2.1 hcase.1 hcase.2
    · exact hrows.2.2.2.2 hcase.1 hcase.2
  have hret := ha.small_norm_retained_gap hK phi a hmon hN8 hc.2.2.2.1
    (fiveRegion_case_disjunction r A B hcase) 48 (19/200) 15 (Or.inr ⟨rfl,rfl,rfl⟩)
  have hret' : (9999/10000 : ℝ)*(200/19)^2*
      (1/R-(51051/400000 : ℝ)/(A^2*B^2))^2*(A^2*T^5/S^2) < C := by
    convert hret.1 using 1 <;>
      dsimp [R,phaseVandermondeRatio,coherentVandermonde3,A,B,S,T,C,f] <;> ring
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hR : 0 < R := by
    dsimp [R,phaseVandermondeRatio]
    apply div_pos _ (by positivity)
    apply norm_pos_iff.mpr
    exact mul_ne_zero (mul_ne_zero
      (sub_ne_zero.mpr ((hf.comp ha.1).ne (by decide : (0 : Fin 5) ≠ 1)))
      (sub_ne_zero.mpr ((hf.comp ha.1).ne (by decide : (0 : Fin 5) ≠ 2))))
      (sub_ne_zero.mpr ((hf.comp ha.1).ne (by decide : (1 : Fin 5) ≠ 2)))
  have hRQ : R ≤ fiveRegionTriangle r := phaseVandermondeRatio_le_ratio_triangle
    (f (a 0)) (f (a 1)) (f (a 2)) (fiveRegionAnchorRatio r)
    (fiveRegionAnchorRatio_nonneg r) hB hBS hc.2.2.2.2.2
  have hphase := coupled_phase_row_bound (f (a 0)) (f (a 1)) (f (a 2))
    (fiveRegionQ r) (fiveRegionPhase r) (fiveRegion_parameters r).2.2.2.2.2.2.2.2.2.2.2.2.2
    hB hBS hc.2.2.2.2.1
  exact fiveRegion_retained_scalar r A B S T C R (phasePhi (f (a 1)) (f (a 2)))
    hA hc.2.2.1 hBS hR hRQ (by unfold phasePhi; positivity) hphase hfront hret'

end D1Bound5
end
