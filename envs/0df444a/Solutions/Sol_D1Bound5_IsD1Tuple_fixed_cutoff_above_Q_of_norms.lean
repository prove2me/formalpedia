-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.fixed_cutoff_above_Q_of_norms
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:14.646266+00:00
-- url     : https://prove2.me/submissions/43471b10-6ced-412d-87e5-8ed7ef61d434

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
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
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_finiteQ_upper_of_lower
import Theorems.Thm_D1Bound5_IsD1Tuple_fixed_cutoff_retained_gap_of_norms
import Theorems.Thm_D1Bound5_OneSmallCutoffRow_start_overlap_real
import Theorems.Thm_D1Bound5_fixed_cutoff_start_above_Q
import Theorems.Thm_D1Bound5_oneSmallCutoffRows_valid
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5




theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (r : OneSmallCutoffRow) (hr : r ∈ oneSmallCutoffRows)
    (hAsq : ‖phi (a 0 : K)‖^2 = (r.a0 : ℝ))
    (hBsq : ‖phi (a 1 : K)‖^2 = (r.b0 : ℝ))
    (hSsq : ‖phi (a 2 : K)‖^2 = (r.s0 : ℝ))
    (hdab : ‖phi (a 0 : K)-phi (a 1 : K)‖^2 = (r.dab : ℝ))
    (hdas : ‖phi (a 0 : K)-phi (a 2 : K)‖^2 = (r.das : ℝ))
    (hdbs : ‖phi (a 1 : K)-phi (a 2 : K)‖^2 = (r.dbs : ℝ))
    (hlarge : (r.triple.cutoff : ℝ) ≤ ‖phi (a 3 : K)‖^2) :
    ‖phi (a 4 : K)‖^7/(9*‖phi (a 3 : K)‖^2*(1+1/4000 : ℝ)) <
      ‖phi (a 5 : K)‖ := by
  let A := ‖phi (a 0 : K)‖
  let S := ‖phi (a 2 : K)‖
  let T := ‖phi (a 3 : K)‖
  let C := ‖phi (a 4 : K)‖
  let D := ‖phi (a 5 : K)‖
  have hA : 1 ≤ A := one_le_norm_integer hK phi (ha.2.1 0)
  have hS : 0 < S := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (one_le_norm_integer hK phi (ha.2.1 2))
  have hT : 0 < T := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (one_le_norm_integer hK phi (ha.2.1 3))
  have hC : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (one_le_norm_integer hK phi (ha.2.1 4))
  have hv := oneSmallCutoffRows_valid r hr
  change S^2 = (r.s0 : ℝ) at hSsq
  have hover := r.start_overlap_real hv S T hS hSsq hlarge
  have hg := IsD1Tuple.fixed_cutoff_retained_gap_of_norms hK phi a ha hmon r hr hAsq hBsq hSsq hdab hdas hdbs hlarge
  have hstart : C^7/(S^2*T^4) < D := by
    have hA2 : 1 ≤ A^2 := by nlinarith only [hA]
    calc
      _ ≤ A^2*C^7/(S^2*T^4) := by
        gcongr
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hA2 (pow_nonneg hC.le 7)
      _ < D := hg.2.2.1
  have hcoefpos : 0 < (r.retainedCoefficient : ℝ) := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hK,_⟩ := hv
    have hh : (1 : ℝ) < (r.retainedCoefficient : ℝ) := by exact_mod_cast hK
    linarith only [hh]
  have hleft := fixed_cutoff_start_above_Q (r.retainedCoefficient : ℝ) S T C D
    hcoefpos hS hT hC hg.1 hstart hover
  exact IsD1Tuple.finiteQ_upper_of_lower hK phi a ha hmon
    hg.2.2.2.1.le hg.2.2.2.2.2.1.le hleft.le


end D1Bound5
end
