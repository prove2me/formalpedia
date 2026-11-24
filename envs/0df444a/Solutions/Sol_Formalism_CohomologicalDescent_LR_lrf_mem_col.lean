-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrf_mem_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:23.338875+00:00
-- url     : https://prove2.me/submissions/0bb791a5-6a8a-442d-b5f8-faeccac404e1

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
theorem _root_.solution (s : Fin n) (l : Fin r × Fin r × (Fin r × Fin n)) :
    (l ∈ (List.finRange r).filterMap fun a =>
      if h : s.val < a.val ∧ s.val < r then some ((⟨s.val, h.2⟩ : Fin r), a, (a, s)) else none) ↔
      l.1.val = s.val ∧ s.val < l.2.1.val ∧ l.2.2 = (l.2.1, s) := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, -, ha⟩
    split_ifs at ha with h
    rw [Option.some.injEq] at ha
    subst ha
    exact ⟨rfl, h.1, rfl⟩
  · obtain ⟨x, a, v⟩ := l
    rintro ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    refine ⟨a, List.mem_finRange a, ?_⟩
    have hr : s.val < r := lt_trans h2 a.isLt
    rw [dif_pos ⟨h2, hr⟩, h3]
    congr 2
    exact Fin.ext h1.symm
end Formalism.CohomologicalDescent.LR
