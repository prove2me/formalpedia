-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_zcomp_bmZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:18.772853+00:00
-- url     : https://prove2.me/submissions/0f5e29d1-331c-436a-a86a-4e3bcb033330

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_whc_shift
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_deriv_monomial_WH
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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (β : Fin n → ℤ) (l j : Fin n) (F : BP R n) :
    zcomp R n (β + (Pi.single l 1 - Pi.single j 1)) (bmZ R n l j F) = bmZ R n l j (zcomp R n β F) := by
  have hf : ∀ v : Fin (n + 1) × Fin n, IsWeightedHomogeneous (zW n)
      ((fun v : Fin (n + 1) × Fin n => if v.2 = j ∧ v.1 = Fin.last n then (X (v.1, l) : BP R n) else 0) v)
      (zW n v + (Pi.single l 1 - Pi.single j 1)) := by
    intro v
    dsimp only
    split_ifs with hv
    · have e : zW n v + (Pi.single l 1 - Pi.single j 1) = zW n (v.1, l) := by
        obtain ⟨a, b⟩ := v
        simp only at hv
        obtain ⟨rfl, rfl⟩ := hv
        simp [zW]
      rw [e]
      apply isWeightedHomogeneous_X
    · apply isWeightedHomogeneous_zero
  exact bm_whc_shift (zW n) _ (bmZ R n l j).toLinearMap (fun m => bm_deriv_monomial_WH (zW n) _ _ hf m) β F
end Formalism.BranchingDeterminantCap
