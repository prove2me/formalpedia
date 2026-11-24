-- Prove2me | solution 1 for FockRaiseLowInner.fockInner_eq_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:10.904916+00:00
-- url     : https://prove2.me/submissions/1f75b015-756c-4430-9591-258fb4d10b8c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Theorems.Thm_FockRaiseLowInner_fockInner_eq_sum

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
theorem _root_.solution (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : P.support ⊆ S) :
    fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by
  refine fockInner_eq_sum P Q S (fun α hα => ?_)
  have h : coeff α P = 0 := by
    by_contra h'
    exact hα (hS (MvPolynomial.mem_support_iff.mpr h'))
  rw [h]
  simp
end FockRaiseLowInner
