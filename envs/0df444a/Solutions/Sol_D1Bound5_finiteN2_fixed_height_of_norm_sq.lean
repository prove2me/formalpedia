-- Prove2me | solution 1 for D1Bound5.finiteN2_fixed_height_of_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:48:28.981993+00:00
-- url     : https://prove2.me/submissions/3544d569-ce70-41bf-a312-b0a385e70ce2

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
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
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions
import Definitions.Def_D1Bound5_FiniteN2Height_Definitions
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallN2FixedArithmetic_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_finiteN2FixedPolynomial_scaled_le
import Theorems.Thm_D1Bound5_finiteN2_root_coeff_decomposition
import Theorems.Thm_D1Bound5_finite_norm_quadratic_le
import Theorems.Thm_D1Bound5_oneSmallCutoffRows_finiteN2FixedBound

section
open scoped NumberField

namespace D1Bound5
open QuadInt

/-- N2 height transfer from actual squared coefficient norms. -/
theorem _root_.solution
    (r : OneSmallCutoffRow) (hr : r ∈ oneSmallCutoffRows)
    (X Y Z : ℂ) (hBsq : ‖Y‖^2 = (r.b0 : ℝ))
    (hnorm : ∀ i j ell, ‖finiteN2FixedPolynomial X Y i j ell‖^2 =
      ((finiteN2FixedPolynomial r.triple.anchorA r.triple.anchorB i j ell).norm : ℝ))
    (hy0 : Y ≠ 0) (hC : 1000 ≤ ‖Z‖) (hCB : 200*‖Y‖ ≤ ‖Z‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteN2Left X Y Z i‖+‖finiteN2Right X Y Z i‖) <
      (r.M2 : ℝ)*‖Y‖^4*‖Z‖^2 := by
  let B := ‖Y‖
  let C := ‖Z‖
  have hB : 0 < B := norm_pos_iff.mpr hy0
  have hC0 : 0 < C := by dsimp [C]; linarith only [hC]
  obtain ⟨w,hw,hsq,hrow⟩ := oneSmallCutoffRows_finiteN2FixedBound r hr
  have hcoef (j : Fin 2) (ell : Fin 3) :
      ‖finiteN2FixedPolynomial X Y i j ell‖*C^(ell : ℕ) ≤
        (w i j ell : ℝ)*B^4*C^2 := by
    have hn := hnorm i j ell
    have hb : ‖finiteN2FixedPolynomial X Y i j ell‖^2 ≤
        if B^2 ≤ 25 then (w i j ell : ℝ)^2*(B^2)^4*1000^(4-2*(ell : ℕ))
        else (w i j ell : ℝ)^2*(B^2)^(6-(ell : ℕ))*200^(4-2*(ell : ℕ)) := by
      rw [hBsq,hn]
      split_ifs with hcase
      · have hc : r.b0 ≤ 25 := by exact_mod_cast hcase
        have h := hsq i j ell
        rw [if_pos hc] at h
        exact_mod_cast h
      · have hc : ¬ r.b0 ≤ 25 := by exact_mod_cast hcase
        have h := hsq i j ell
        rw [if_neg hc] at h
        exact_mod_cast h
    exact finiteN2FixedPolynomial_scaled_le B C (w i j ell : ℝ)
      ‖finiteN2FixedPolynomial X Y i j ell‖ ell hB hC hCB
      (by exact_mod_cast hw i j ell) (norm_nonneg _) hb
  have hcolumn (j : Fin 2) :
      ‖![finiteN2Left X Y Z i,finiteN2Right X Y Z i] j‖ ≤
        ((w i j 0 : ℝ)+(w i j 1 : ℝ)+(w i j 2 : ℝ))*B^4*C^2 := by
    rw [finiteN2_root_coeff_decomposition]
    have hh := finite_norm_quadratic_le
      (finiteHomogeneousTwo 2 (finiteN2Coeff0 i j) X Y)
      (finiteHomogeneousTwo 3 (finiteN2Coeff1 i j) X Y)
      (finiteHomogeneousTwo 4 (finiteN2Coeff2 i j) X Y) Z
    have h0 := hcoef j 0
    have h1 := hcoef j 1
    have h2 := hcoef j 2
    norm_num [finiteN2FixedPolynomial] at h0 h1 h2
    change ‖finiteHomogeneousTwo 4 (finiteN2Coeff2 i j) X Y‖*C^2 ≤
      (w i j 2 : ℝ)*B^4*C^2 at h2
    change ‖finiteHomogeneousTwo 2 (finiteN2Coeff0 i j) X Y+
      finiteHomogeneousTwo 3 (finiteN2Coeff1 i j) X Y*Z+
      finiteHomogeneousTwo 4 (finiteN2Coeff2 i j) X Y*Z^2‖ ≤
      ‖finiteHomogeneousTwo 2 (finiteN2Coeff0 i j) X Y‖+
      ‖finiteHomogeneousTwo 3 (finiteN2Coeff1 i j) X Y‖*C+
      ‖finiteHomogeneousTwo 4 (finiteN2Coeff2 i j) X Y‖*C^2 at hh
    nlinarith only [hh,h0,h1,h2]
  have hsum := add_le_add (hcolumn 0) (hcolumn 1)
  change ‖finiteN2Left X Y Z i‖+‖finiteN2Right X Y Z i‖ ≤ _ at hsum
  have hheight : (101/100 : ℝ)*
      ((w i 0 0 : ℝ)+(w i 0 1 : ℝ)+(w i 0 2 : ℝ)+
        ((w i 1 0 : ℝ)+(w i 1 1 : ℝ)+(w i 1 2 : ℝ))) < (r.M2 : ℝ) := by
    have hh : (101/100 : ℝ)*(∑ j, ∑ ell, (w i j ell : ℝ)) < (r.M2 : ℝ) := by
      have hhq := (Rat.cast_lt (K := ℝ)).2 (hrow i)
      push_cast at hhq
      exact hhq
    simpa [Fin.sum_univ_succ,add_assoc] using hh
  have hfirst := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 101/100)
  have hlast := mul_lt_mul_of_pos_right hheight (by positivity : 0 < B^4*C^2)
  nlinarith only [hfirst,hlast]



end D1Bound5
end
