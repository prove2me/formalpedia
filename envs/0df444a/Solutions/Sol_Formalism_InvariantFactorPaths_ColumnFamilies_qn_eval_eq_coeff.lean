-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_eval_eq_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:18.168571+00:00
-- url     : https://prove2.me/submissions/8e95ce01-c8e6-412e-8633-6a3f0381b73e

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_diag
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_mnu_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (ν : Fin n → ℕ) (F : MvPolynomial (Fin n × Fin n) ℚ)
    (hF : IsWeightedHomogeneous (colW n n) F ν) :
    eval (idFrame ℚ n n) F = coeff (lhwline_mnu (le_refl n) ν) F := by
  have hD : ∀ (a : Fin n) (j : Fin n), a.val ≠ j.val → idFrame ℚ n n (a, j) = 0 := by
    intro a j h
    simp [idFrame, h]
  rw [lhwline_diag (le_refl n) ν F hF (idFrame ℚ n n) hD]
  have : ∏ v, idFrame ℚ n n v ^ (lhwline_mnu (le_refl n) ν) v = 1 := by
    refine Finset.prod_eq_one fun v _ => ?_
    obtain ⟨a, j⟩ := v
    rw [lhwline_mnu_apply]
    by_cases h : a.val = j.val
    · simp [idFrame, h]
    · simp [h]
  rw [this, mul_one]
end Formalism.InvariantFactorPaths.ColumnFamilies
