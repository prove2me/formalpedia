-- Prove2me | solution 1 for FockRaiseLowInner.fockInner_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:44.317868+00:00
-- url     : https://prove2.me/submissions/2cae267c-8f79-401e-a947-4673472ac0ff

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Theorems.Thm_FockRaiseLowInner_fockInner_zero_right
import Theorems.Thm_FockRaiseLowInner_fockInner_add_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockRaiseLowInner
open MvPolynomial FockH1Action
variable {σ : Type*}
namespace FockRaiseLowInner
theorem _root_.solution {ι : Type*} (s : Finset ι) (P : MvPolynomial σ ℂ)
    (f : ι → MvPolynomial σ ℂ) :
    fockInner P (∑ i ∈ s, f i) = ∑ i ∈ s, fockInner P (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, fockInner_zero_right]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fockInner_add_right, ih]
end FockRaiseLowInner
