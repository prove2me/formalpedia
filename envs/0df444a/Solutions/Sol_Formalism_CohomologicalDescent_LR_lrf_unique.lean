-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrf_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:30.400126+00:00
-- url     : https://prove2.me/submissions/6bf91981-8525-42e5-9a14-2bc4d1ddf5dc

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (m e : Fin r × Fin n →₀ ℕ) (hm : LowerTri m) (he : LowerTri e) (hoff : lrf_off m = lrf_off e)
    (hcol : ∀ s : Fin n, ∑ a : Fin r, m (a, s) = ∑ a : Fin r, e (a, s)) : m = e := by
  classical
  have hlow : ∀ (a : Fin r) (s : Fin n), s.val < a.val → m (a, s) = e (a, s) := by
    intro a s h
    have h1 := DFunLike.congr_fun hoff (a, s)
    simpa [lrf_off, Finsupp.filter_apply, h] using h1
  have hne : ∀ (a : Fin r) (s : Fin n), a.val ≠ s.val → m (a, s) = e (a, s) := by
    intro a s h
    rcases lt_or_gt_of_ne h with h' | h'
    · rw [hm a s h', he a s h']
    · exact hlow a s h'
  ext ⟨a, s⟩
  by_cases h : a.val = s.val
  · have h1 := hcol s
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ (fun a => e (a, s)) (Finset.mem_univ a)] at h1
    have h2 : ∑ x ∈ Finset.univ.erase a, m (x, s) = ∑ x ∈ Finset.univ.erase a, e (x, s) := by
      refine Finset.sum_congr rfl fun x hx => hne x s ?_
      intro hxs
      exact (Finset.ne_of_mem_erase hx) (Fin.ext (by omega))
    omega
  · exact hne a s h
end Formalism.CohomologicalDescent.LR
