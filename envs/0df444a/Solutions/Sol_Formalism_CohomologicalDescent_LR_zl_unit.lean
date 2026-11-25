-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.zl_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:34:54.652042+00:00
-- url     : https://prove2.me/submissions/2d353c08-4c45-4dfb-b581-b0838eda0ce6

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrcFockZeroRight
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
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution {l : ℕ} (hl : l.Prime) (m : ℤ) (hm : ¬ (l : ℤ) ∣ m) : IsUnit (m : Zl l) := by
  have hm0 : (m : ℚ) ≠ 0 := by
    intro h
    have : m = 0 := by exact_mod_cast h
    subst this
    exact hm (dvd_zero _)
  refine IsUnit.of_mul_eq_one (⟨(m : ℚ)⁻¹, lrc_inv_mem hl m hm⟩ : Zl l) ?_
  apply Subtype.ext
  simp [hm0]
end Formalism.CohomologicalDescent.LR
