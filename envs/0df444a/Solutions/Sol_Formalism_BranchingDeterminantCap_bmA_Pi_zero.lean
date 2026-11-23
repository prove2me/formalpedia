-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmA_Pi_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:32.589801+00:00
-- url     : https://prove2.me/submissions/914f94c0-974c-43b8-8dce-4751d5f1ce3c

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_Pi_perm
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
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (E : Fin n → Fin n → Module.End R M) (u : ℤ)
    (hE : ∀ i j k l, E i j * E k l - E k l * E i j = (if j = k then E i l else 0) - (if i = l then E k j else 0))
    (h2 : ∀ x : Module.End R M, x + x = 0 → x = 0) (β : Fin n → Fin n) (k l : Fin n) (hkl : k ≠ l)
    (hβ : β k = β l) : bmPi E u β = 0 := by
  have h := bmA_Pi_perm E u hE h2 (Equiv.swap k l) β
  have e : β ∘ Equiv.swap k l = β := by
    funext x
    simp only [Function.comp_apply]
    by_cases hx : x = k
    · subst hx
      rw [Equiv.swap_apply_left, hβ]
    · by_cases hx' : x = l
      · subst hx'
        rw [Equiv.swap_apply_right, hβ]
      · rw [Equiv.swap_apply_of_ne_of_ne hx hx']
  rw [e, Equiv.Perm.sign_swap hkl] at h
  simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] at h
  apply h2
  nth_rewrite 1 [h]
  exact neg_add_cancel _
end Formalism.BranchingDeterminantCap
