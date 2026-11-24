-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:16:19.720718+00:00
-- url     : https://prove2.me/submissions/26389294-b98a-4415-aa12-ad8c7bf99128

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_rank_two_vector_def
import Theorems.Thm_Formalism_CohomologicalDescent_LD_leading_minor_one_eq_entry
import Theorems.Thm_Formalism_CohomologicalDescent_LD_leading_minor_two_eq_det
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (w y : ℕ) : hw ℤ (le_refl 2) (wt2 w y) = vec2 w y 0 := by
  unfold hw
  rw [Fin.prod_univ_two]
  simp only [Fin.val_zero, Fin.val_one, zero_add, Nat.reduceAdd]
  rw [leading_minor_one_eq_entry, leading_minor_two_eq_det, rank_two_vector_def]
  simp [nuNext, wt2]
end Formalism.CohomologicalDescent.LD
