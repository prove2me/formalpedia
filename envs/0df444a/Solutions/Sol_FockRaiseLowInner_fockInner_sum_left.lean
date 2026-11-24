-- Prove2me | solution 1 for FockRaiseLowInner.fockInner_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:28.553907+00:00
-- url     : https://prove2.me/submissions/4e1748df-90e5-41d3-b947-16718efdd081

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Theorems.Thm_FockRaiseLowInner_fockInner_zero_left
import Theorems.Thm_FockRaiseLowInner_fockInner_add_left

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
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (Q : MvPolynomial σ ℂ) :
    fockInner (∑ i ∈ s, f i) Q = ∑ i ∈ s, fockInner (f i) Q := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, fockInner_zero_left]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fockInner_add_left, ih]
end FockRaiseLowInner
