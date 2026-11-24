-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.labelLHS_shift_to_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:11:16.325222+00:00
-- url     : https://prove2.me/submissions/d6d7dffe-08dd-45da-9b94-97fe7a5871b5

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
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
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.UnitNormBounds
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
namespace Formalism.CohomologicalDescent.UnitNormBounds
theorem _root_.solution (l k t : ℕ) (i : ℝ) (xm xp mB : ℤ) :
    labelLHS l k t i xm xp mB = labelLHS l k t i (xm - mB) (xp - mB) 0 := by
  unfold labelLHS
  congr 1
  · refine Finset.sum_nbij' (fun ct => ct - mB) (fun ct => ct + mB) ?_ ?_ ?_ ?_ ?_
    · intro ct h
      simp only [Finset.mem_Icc] at h ⊢
      omega
    · intro ct h
      simp only [Finset.mem_Icc] at h ⊢
      omega
    · intro ct _
      ring
    · intro ct _
      ring
    · intro ct _
      rw [sub_zero]
  · refine Finset.sum_nbij' (fun ct => ct - mB) (fun ct => ct + mB) ?_ ?_ ?_ ?_ ?_
    · intro ct h
      simp only [Finset.mem_Ioo] at h ⊢
      omega
    · intro ct h
      simp only [Finset.mem_Ioo] at h ⊢
      omega
    · intro ct _
      ring
    · intro ct _
      ring
    · intro ct _
      have e1 : xm - mB - (ct - mB) = xm - ct := by ring
      rw [e1, sub_zero]
end Formalism.CohomologicalDescent.UnitNormBounds
