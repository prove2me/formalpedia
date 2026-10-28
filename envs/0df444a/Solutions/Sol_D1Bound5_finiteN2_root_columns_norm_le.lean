-- Prove2me | solution 1 for D1Bound5.finiteN2_root_columns_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:33.062476+00:00
-- url     : https://prove2.me/submissions/1cedc2fd-7f65-43b5-a875-58ddb8740325

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
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions
import Definitions.Def_D1Bound5_FiniteN2Height_Definitions
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions
import Theorems.Thm_D1Bound5_finiteHomogeneousTwo_norm_le
import Theorems.Thm_D1Bound5_finiteN2_coefficient_sums
import Theorems.Thm_D1Bound5_finiteN2_root_coeff_decomposition
import Theorems.Thm_D1Bound5_finite_norm_quadratic_le

section
namespace D1Bound5











theorem _root_.solution (x y c : ℂ) (hxy : ‖x‖ ≤ ‖y‖) (i : Fin 3) :
    ‖finiteN2Left x y c i‖+‖finiteN2Right x y c i‖ ≤
      50*‖y‖^2+200*‖y‖^3*‖c‖+240*‖y‖^4*‖c‖^2 := by
  have hroot (j : Fin 2) :
      ‖![finiteN2Left x y c i,finiteN2Right x y c i] j‖ ≤
        (∑ r, |(finiteN2Coeff0 i j r : ℝ)|)*‖y‖^2 +
        (∑ r, |(finiteN2Coeff1 i j r : ℝ)|)*‖y‖^3*‖c‖ +
        (∑ r, |(finiteN2Coeff2 i j r : ℝ)|)*‖y‖^4*‖c‖^2 := by
    rw [finiteN2_root_coeff_decomposition]
    apply (finite_norm_quadratic_le _ _ _ _).trans
    have h0 := finiteHomogeneousTwo_norm_le 2 (finiteN2Coeff0 i j) x y hxy
    have h1 := finiteHomogeneousTwo_norm_le 3 (finiteN2Coeff1 i j) x y hxy
    have h2 := finiteHomogeneousTwo_norm_le 4 (finiteN2Coeff2 i j) x y hxy
    gcongr
  obtain ⟨h0,h1,h2⟩ := finiteN2_coefficient_sums i
  have h := add_le_add (hroot 0) (hroot 1)
  change ‖finiteN2Left x y c i‖+‖finiteN2Right x y c i‖ ≤ _ at h
  calc
    _ ≤ _ := h
    _ = ((∑ r, |(finiteN2Coeff0 i 0 r : ℝ)|)+
          (∑ r, |(finiteN2Coeff0 i 1 r : ℝ)|))*‖y‖^2 +
        ((∑ r, |(finiteN2Coeff1 i 0 r : ℝ)|)+
          (∑ r, |(finiteN2Coeff1 i 1 r : ℝ)|))*‖y‖^3*‖c‖ +
        ((∑ r, |(finiteN2Coeff2 i 0 r : ℝ)|)+
          (∑ r, |(finiteN2Coeff2 i 1 r : ℝ)|))*‖y‖^4*‖c‖^2 := by ring
    _ ≤ _ := by gcongr





end D1Bound5
end
