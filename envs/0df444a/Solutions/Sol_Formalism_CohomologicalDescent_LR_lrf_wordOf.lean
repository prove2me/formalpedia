-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrf_wordOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:30.696596+00:00
-- url     : https://prove2.me/submissions/eeca911c-6236-4f98-a11c-4e1a91c57076

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
theorem _root_.solution (e d : Fin r × Fin n →₀ ℕ) (h : ∀ (a : Fin r) (s : Fin n), s.val < a.val → d (a, s) = e (a, s)) :
    (lrf_L r n).map (fun l => (l.1, l.2.1, d l.2.2)) = wordOf e := by
  unfold lrf_L wordOf
  rw [List.map_flatMap]
  congr 1
  funext s
  rw [List.map_filterMap]
  congr 1
  funext a
  split_ifs with h'
  · simp [h a s h'.1]
  · rfl
end Formalism.CohomologicalDescent.LR
