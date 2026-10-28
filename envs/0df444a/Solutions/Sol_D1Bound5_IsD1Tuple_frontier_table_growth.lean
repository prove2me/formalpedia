-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.frontier_table_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:47:17.213574+00:00
-- url     : https://prove2.me/submissions/9e604d0f-07fe-4e68-8e51-0eb5fce149b4

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FrontierScalarReduction_Definitions
import Definitions.Def_D1Bound5_FrontierTableNumeric_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_Regular_Definitions
import Theorems.Thm_D1Bound5_FrontierTableRow_parameters
import Theorems.Thm_D1Bound5_IsD1Tuple_frontier_determinant_envelope
import Theorems.Thm_D1Bound5_IsD1Tuple_tail_irregular_and_growth
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_frontier_scalar_reduction
import Theorems.Thm_D1Bound5_frontier_table_numeric

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5



/-- All five small-first-entry frontier table rows hold for actual ordered
D(1)-quadruples. The rational lower bounds and row thresholds are explicit. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 4 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (alpha beta target : ℝ) (hrow : FrontierTableRow alpha beta target)
    (hA : alpha ≤ ‖phi (a 0 : K)‖) (hB : beta ≤ ‖phi (a 1 : K)‖)
    (hsmall : ‖phi (a 0 : K)‖ < 3) :
    target*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖ < ‖phi (a 3 : K)‖ := by
  obtain ⟨halpha,hbeta,hab,hprod,hKK,hLL,hQQ⟩ := hrow.parameters
  let A := ‖phi (a 0 : K)‖
  let B := ‖phi (a 1 : K)‖
  let C := ‖phi (a 2 : K)‖
  let D := ‖phi (a 3 : K)‖
  have hbeta0 : 0 < beta := by linarith only [hbeta]
  have hA0 : 0 < A := halpha.trans_le hA
  have hB0 : 0 < B := hbeta0.trans_le hB
  have hC : beta ≤ C := hB.trans (hmon (by decide : (1 : Fin 4) ≤ 2))
  have hC0 : 0 < C := hbeta0.trans_le hC
  have hABC : 0 < A*B*C := by positivity
  have hupper := IsD1Tuple.frontier_determinant_envelope hK phi a ha hmon
    alpha beta halpha hbeta0 hab hprod.le hA hB
  have hscalar := frontier_scalar_reduction A B C D alpha beta
    (frontierK alpha beta) (frontierL alpha beta) (frontierQ alpha beta)
    halpha hbeta0 hA hB hC (norm_nonneg _) hKK hLL hQQ hupper
  have htail : 2*B*C < D :=
    (ha.tail_irregular_and_growth hK phi a hmon (hbeta.trans hB)).2
  have htau : (2/3 : ℝ) < D/(A*B*C) := by
    apply (lt_div_iff₀ hABC).mpr
    have hp := mul_pos (sub_pos.mpr hsmall) (mul_pos hB0 hC0)
    nlinarith only [htail,hp]
  have hresult := frontier_table_numeric alpha beta target (D/(A*B*C)) hrow htau
    (by simpa only [frontierP, frontierJ] using hscalar)
  have h := (lt_div_iff₀ hABC).mp hresult
  change target*A*B*C < D
  nlinarith only [h]

end D1Bound5
end
