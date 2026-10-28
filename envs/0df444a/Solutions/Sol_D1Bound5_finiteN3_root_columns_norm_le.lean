-- Prove2me | solution 1 for D1Bound5.finiteN3_root_columns_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:30.549245+00:00
-- url     : https://prove2.me/submissions/01fee82e-d2b0-4999-a11a-d5dc8a5061d4

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
import Definitions.Def_D1Bound5_FiniteN3Height_Definitions
import Definitions.Def_D1Bound5_FiniteN3Matrix_Definitions
import Theorems.Thm_D1Bound5_finiteHomogeneousTwo_norm_le
import Theorems.Thm_D1Bound5_finiteN3_coefficient_sums
import Theorems.Thm_D1Bound5_finiteN3_root_coeff_decomposition
import Theorems.Thm_D1Bound5_finite_norm_quadratic_le

section
namespace D1Bound5










theorem finite_norm_cubic_le (u v w t c : ℂ) :
    ‖u+v*c+w*c^2+t*c^3‖ ≤
      ‖u‖+‖v‖*‖c‖+‖w‖*‖c‖^2+‖t‖*‖c‖^3 := by
  calc
    _ ≤ ‖u+v*c+w*c^2‖+‖t*c^3‖ := norm_add_le _ _
    _ ≤ (‖u‖+‖v‖*‖c‖+‖w‖*‖c‖^2)+‖t*c^3‖ :=
      add_le_add (finite_norm_quadratic_le _ _ _ _) le_rfl
    _ = _ := by rw [norm_mul,norm_pow]





theorem _root_.solution (x y c : ℂ) (hxy : ‖x‖ ≤ ‖y‖) (i : Fin 3) :
    ‖finiteN3Left x y c i‖+‖finiteN3Right x y c i‖ ≤
      342*‖y‖^4+2352*‖y‖^5*‖c‖+5792*‖y‖^6*‖c‖^2+4096*‖y‖^7*‖c‖^3 := by
  have hroot (j : Fin 2) :
      ‖![finiteN3Left x y c i,finiteN3Right x y c i] j‖ ≤
        (∑ r, |(finiteN3Coeff0 i j r : ℝ)|)*‖y‖^4 +
        (∑ r, |(finiteN3Coeff1 i j r : ℝ)|)*‖y‖^5*‖c‖ +
        (∑ r, |(finiteN3Coeff2 i j r : ℝ)|)*‖y‖^6*‖c‖^2 +
        (∑ r, |(finiteN3Coeff3 i j r : ℝ)|)*‖y‖^7*‖c‖^3 := by
    rw [finiteN3_root_coeff_decomposition]
    apply (finite_norm_cubic_le _ _ _ _ _).trans
    have h0 := finiteHomogeneousTwo_norm_le 4 (finiteN3Coeff0 i j) x y hxy
    have h1 := finiteHomogeneousTwo_norm_le 5 (finiteN3Coeff1 i j) x y hxy
    have h2 := finiteHomogeneousTwo_norm_le 6 (finiteN3Coeff2 i j) x y hxy
    have h3 := finiteHomogeneousTwo_norm_le 7 (finiteN3Coeff3 i j) x y hxy
    gcongr
  obtain ⟨h0,h1,h2,h3⟩ := finiteN3_coefficient_sums i
  have h := add_le_add (hroot 0) (hroot 1)
  change ‖finiteN3Left x y c i‖+‖finiteN3Right x y c i‖ ≤ _ at h
  calc
    _ ≤ _ := h
    _ = ((∑ r, |(finiteN3Coeff0 i 0 r : ℝ)|)+
          (∑ r, |(finiteN3Coeff0 i 1 r : ℝ)|))*‖y‖^4 +
        ((∑ r, |(finiteN3Coeff1 i 0 r : ℝ)|)+
          (∑ r, |(finiteN3Coeff1 i 1 r : ℝ)|))*‖y‖^5*‖c‖ +
        ((∑ r, |(finiteN3Coeff2 i 0 r : ℝ)|)+
          (∑ r, |(finiteN3Coeff2 i 1 r : ℝ)|))*‖y‖^6*‖c‖^2 +
        ((∑ r, |(finiteN3Coeff3 i 0 r : ℝ)|)+
          (∑ r, |(finiteN3Coeff3 i 1 r : ℝ)|))*‖y‖^7*‖c‖^3 := by ring
    _ ≤ _ := by gcongr





end D1Bound5
end
