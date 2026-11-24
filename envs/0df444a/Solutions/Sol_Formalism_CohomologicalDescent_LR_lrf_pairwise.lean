-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrf_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:00.847811+00:00
-- url     : https://prove2.me/submissions/dffcd05e-a0e2-441e-855f-8c9c9088e59e

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_mem_col
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
theorem _root_.solution :
    (lrf_L r n).Pairwise fun l l' => l.2.2 ≠ l'.2.2 ∧ l.2.1 ≠ l'.1 := by
  unfold lrf_L
  rw [List.pairwise_flatMap]
  constructor
  · intro s _
    rw [List.pairwise_filterMap]
    refine (List.sortedLT_finRange r).pairwise.imp ?_
    intro a a' haa b hb b' hb'
    split_ifs at hb with h
    split_ifs at hb' with h'
    rw [Option.some.injEq] at hb hb'
    subst hb
    subst hb'
    refine ⟨fun e => ?_, fun e => ?_⟩
    · exact (ne_of_lt haa) (congrArg Prod.fst e)
    · have := congrArg Fin.val e
      simp only at this
      omega
  · rw [List.pairwise_reverse]
    refine (List.sortedLT_finRange n).pairwise.imp ?_
    intro s s' hss x hx y hy
    rw [lrf_mem_col] at hx hy
    refine ⟨fun e => ?_, fun e => ?_⟩
    · rw [hx.2.2, hy.2.2] at e
      exact (ne_of_gt hss) (congrArg Prod.snd e)
    · have := congrArg Fin.val e
      have h3 : s.val < s'.val := hss
      omega
end Formalism.CohomologicalDescent.LR
