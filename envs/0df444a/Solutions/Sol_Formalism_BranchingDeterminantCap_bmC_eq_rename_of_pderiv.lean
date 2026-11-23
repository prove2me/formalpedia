-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmC_eq_rename_of_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:54.554903+00:00
-- url     : https://prove2.me/submissions/213cd534-bcc1-4415-9e15-1299dbb71080

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmC_ndEv_rename

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {r n : ℕ}
    (H : MvPolynomial (Option (Fin r × Fin n)) R) (h : pderiv none H = 0) :
    H = rename some (ndEv R r n H) := by
  have hsupp : ∀ m ∈ H.support, m none = 0 := by
    intro m hm
    by_contra hne
    have hle : Finsupp.single none 1 ≤ m := by
      rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.2 hne
    have hm' : m = (m - Finsupp.single none 1) + Finsupp.single none 1 := (tsub_add_cancel_of_le hle).symm
    have h1 := congrArg (coeff (m - Finsupp.single none 1)) h
    rw [coeff_pderiv, ← hm', coeff_zero] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact (mem_support_iff.1 hm) h2
    · exact absurd h2 (Nat.cast_add_one_ne_zero _)
  have hv : (↑H.vars : Set (Option (Fin r × Fin n))) ⊆ Set.range some := by
    intro i hi
    rw [Finset.mem_coe, mem_vars_iff_mem_support] at hi
    obtain ⟨m, hm, him⟩ := hi
    cases i with
    | none => exact absurd (hsupp m hm) (Finsupp.mem_support_iff.1 him)
    | some v => exact ⟨v, rfl⟩
  obtain ⟨q, hq⟩ := exists_rename_eq_of_vars_subset_range H some (Option.some_injective _) hv
  rw [← hq, bmC_ndEv_rename]
end Formalism.BranchingDeterminantCap
