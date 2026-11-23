-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_rowAct_var_WH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:22.114668+00:00
-- url     : https://prove2.me/submissions/f2ecb62d-fd90-4fb5-b63c-15b3afe947b7

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_extendMatrix_last_right_zero
import Theorems.Thm_Formalism_BranchingDeterminantCap_extendMatrix_last_left_zero
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
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
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (R : Type*) [CommRing R] {n : ℕ} {B : Type*} [AddCommMonoid B]
    (w : Fin (n + 1) × Fin n → B) (hw : ∀ a b s : Fin n, w (a.castSucc, s) = w (b.castSucc, s))
    (g : Matrix (Fin n) (Fin n) R) (v : Fin (n + 1) × Fin n) :
    IsWeightedHomogeneous w (∑ b : Fin (n + 1), C (extM R g v.1 b) * (X (b, v.2) : BP R n)) (w v) := by
  refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
  by_cases hb : extM R g v.1 b = 0
  · rw [hb, map_zero, zero_mul]
    apply isWeightedHomogeneous_zero
  · have e : w (b, v.2) = w v := by
      obtain ⟨a, s⟩ := v
      by_cases ha : a = Fin.last n
      · subst ha
        by_cases hbl : b = Fin.last n
        · rw [hbl]
        · exact absurd (extendMatrix_last_left_zero R g b hbl) hb
      · by_cases hbl : b = Fin.last n
        · exact absurd (hbl ▸ extendMatrix_last_right_zero R g a ha) hb
        · obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.mpr ha
          obtain ⟨b', rfl⟩ := Fin.exists_castSucc_eq.mpr hbl
          exact hw b' a' s
    rw [← e]
    have hC : IsWeightedHomogeneous w (C (extM R g v.1 b) : BP R n) 0 := by
      apply isWeightedHomogeneous_C
    have hX : IsWeightedHomogeneous w (X (b, v.2) : BP R n) (w (b, v.2)) := by
      apply isWeightedHomogeneous_X
    simpa using hC.mul hX
end Formalism.BranchingDeterminantCap
