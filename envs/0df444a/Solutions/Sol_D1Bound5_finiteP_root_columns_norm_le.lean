-- Prove2me | solution 1 for D1Bound5.finiteP_root_columns_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:05.470989+00:00
-- url     : https://prove2.me/submissions/d260fb65-1024-41f2-a600-1890c8a5786c

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePHeight_Definitions
import Theorems.Thm_D1Bound5_finitePRootColumn_coeff
import Theorems.Thm_D1Bound5_finitePTermValue_norm_le
import Theorems.Thm_D1Bound5_finite_norm_quadratic_le

section
open Finset

namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three



















theorem finitePRootCoeff_norm_le (a b s : ℂ) (hA : 1 ≤ ‖a‖)
    (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖)
    (i : Fin 4) (l j : Fin 3) :
    ‖finitePRootCoeff a b s i l j‖ ≤
      (∑ t, |((finitePRootTerms i l j t).1 : ℝ)|)*
        max (‖b‖*‖s‖^3) (‖b‖^3*‖s‖^2) := by
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun t _ => finitePTermValue_norm_le a b s hA hAB hBS i l j t

theorem finitePRootTerms_sums (i : Fin 4) :
    (∑ j, ∑ t, |((finitePRootTerms i 0 j t).1 : ℝ)|) ≤ 492 ∧
    (∑ j, ∑ t, |((finitePRootTerms i 1 j t).1 : ℝ)|) ≤ 2424 ∧
    (∑ j, ∑ t, |((finitePRootTerms i 2 j t).1 : ℝ)|) ≤ 2352 := by
  fin_cases i <;> norm_num [finitePRootTerms, Fin.sum_univ_succ]

/-- Uniform actual root-column height, including the cancellation in H,V. -/
theorem _root_.solution (a b s c : ℂ) (hA : 1 ≤ ‖a‖)
    (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖) (i : Fin 4) :
    (∑ j, ‖finitePRootColumn a b s c i j‖) ≤
      max (‖b‖*‖s‖^3) (‖b‖^3*‖s‖^2)*(492+2424*‖c‖+2352*‖c‖^2) := by
  let H := max (‖b‖*‖s‖^3) (‖b‖^3*‖s‖^2)
  have hH : 0 ≤ H := le_trans (by positivity) (le_max_left _ _)
  have hj (j : Fin 3) :
      ‖finitePRootColumn a b s c i j‖ ≤
        (∑ t, |((finitePRootTerms i 0 j t).1 : ℝ)|)*H+
        (∑ t, |((finitePRootTerms i 1 j t).1 : ℝ)|)*H*‖c‖+
        (∑ t, |((finitePRootTerms i 2 j t).1 : ℝ)|)*H*‖c‖^2 := by
    rw [finitePRootColumn_coeff]
    apply (finite_norm_quadratic_le _ _ _ _).trans
    have h0 := finitePRootCoeff_norm_le a b s hA hAB hBS i 0 j
    have h1 := finitePRootCoeff_norm_le a b s hA hAB hBS i 1 j
    have h2 := finitePRootCoeff_norm_le a b s hA hAB hBS i 2 j
    dsimp [H] at *
    gcongr
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun j _ => hj j
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  simp only [← Finset.sum_mul] at hsum
  obtain ⟨h0,h1,h2⟩ := finitePRootTerms_sums i
  calc
    _ ≤ _ := hsum
    _ ≤ 492*H+2424*H*‖c‖+2352*H*‖c‖^2 := by gcongr
    _ = _ := by ring





end D1Bound5
end
