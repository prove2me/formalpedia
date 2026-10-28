-- Prove2me | solution 1 for D1Bound5.finiteA4_fixed_height_of_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:44:32.521928+00:00
-- url     : https://prove2.me/submissions/835a6ade-d563-4023-97db-042a266496dd

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteA4Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteA4FixedHeight_Definitions
import Definitions.Def_D1Bound5_FiniteA4Matrix_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_finiteA4RootCoeff_scaled_le
import Theorems.Thm_D1Bound5_finiteA4_root_coeff_decomposition
import Theorems.Thm_D1Bound5_finitePolynomial_norm_le

section
open scoped NumberField

namespace D1Bound5
open QuadInt

/-- Exact coefficient norm identities suffice for height transfer; no
identification of the ambient field with a coordinate ring is needed. -/
theorem _root_.solution {tau nu : ℤ}
    (a b : QuadInt tau nu) (M : ℚ)
    (w : Fin 3 → Fin 2 → Fin 5 → ℚ) (hbound : FiniteA4FixedBound a b M w)
    (X Y Z : ℂ) (hBsq : ‖Y‖^2 = (b.norm : ℝ))
    (hnorm : ∀ i j ell, ‖finiteA4RootCoeff X Y i j ell‖^2 =
      ((finiteA4RootCoeff a b i j ell).norm : ℝ))
    (hy0 : Y ≠ 0) (hC : 1000 ≤ ‖Z‖) (hCB : 200*‖Y‖ ≤ ‖Z‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteA4Left X Y Z i‖+‖finiteA4Right X Y Z i‖) <
      (M : ℝ)*‖Y‖^9*‖Z‖^4 := by
  let B := ‖Y‖
  let C := ‖Z‖
  have hB : 0 < B := norm_pos_iff.mpr hy0
  have hC0 : 0 < C := by dsimp [C]; linarith only [hC]
  obtain ⟨hw,hsq,hrow⟩ := hbound
  have hcoef (j : Fin 2) (ell : Fin 5) :
      ‖finiteA4RootCoeff X Y i j ell‖*C^(ell : ℕ) ≤
        (w i j ell : ℝ)*B^9*C^4 := by
    have hn := hnorm i j ell
    have hb : ‖finiteA4RootCoeff X Y i j ell‖^2 ≤
        if B^2 ≤ 25 then (w i j ell : ℝ)^2*(B^2)^9*1000^(8-2*(ell : ℕ))
        else (w i j ell : ℝ)^2*(B^2)^(13-(ell : ℕ))*200^(8-2*(ell : ℕ)) := by
      rw [hBsq,hn]
      split_ifs with hcase
      · have hc : b.norm ≤ 25 := by exact_mod_cast hcase
        have h := hsq i j ell
        rw [if_pos hc] at h
        exact_mod_cast h
      · have hc : ¬ b.norm ≤ 25 := by exact_mod_cast hcase
        have h := hsq i j ell
        rw [if_neg hc] at h
        exact_mod_cast h
    exact finiteA4RootCoeff_scaled_le B C (w i j ell : ℝ)
      ‖finiteA4RootCoeff X Y i j ell‖ ell hB hC hCB
      (by exact_mod_cast hw i j ell) (norm_nonneg _) hb
  have hcolumn (j : Fin 2) :
      ‖![finiteA4Left X Y Z i,finiteA4Right X Y Z i] j‖ ≤
        (∑ ell, (w i j ell : ℝ))*B^9*C^4 := by
    rw [finiteA4_root_coeff_decomposition]
    apply (finitePolynomial_norm_le 4 (finiteA4RootCoeff X Y i j) Z).trans
    calc
      _ ≤ ∑ ell, (w i j ell : ℝ)*B^9*C^4 := Finset.sum_le_sum (fun ell _ => hcoef j ell)
      _ = _ := by rw [Finset.sum_mul,Finset.sum_mul]
  have hsum := add_le_add (hcolumn 0) (hcolumn 1)
  change ‖finiteA4Left X Y Z i‖+‖finiteA4Right X Y Z i‖ ≤ _ at hsum
  have hheight : (101/100 : ℝ)*((∑ ell, (w i 0 ell : ℝ))+
      (∑ ell, (w i 1 ell : ℝ))) < (M : ℝ) := by
    have hh : (101/100 : ℝ)*(∑ j, ∑ ell, (w i j ell : ℝ)) < (M : ℝ) := by
      have hhq := (Rat.cast_lt (K := ℝ)).2 (hrow i)
      push_cast at hhq
      exact hhq
    simpa only [Fin.sum_univ_two] using hh
  have hfirst := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 101/100)
  have hlast := mul_lt_mul_of_pos_right hheight (by positivity : 0 < B^9*C^4)
  nlinarith only [hfirst,hlast]



end D1Bound5
end
