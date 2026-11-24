-- Prove2me | solution 1 for FockRaiseLowInner.fockInner_neg_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:31.531144+00:00
-- url     : https://prove2.me/submissions/a8ce807c-e411-4c60-800c-fa6d62d7e8f5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Theorems.Thm_FockRaiseLowInner_fockInner_eq_sum_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace FockRaiseLowInner
open MvPolynomial FockH1Action
variable {σ : Type*}
private theorem fockInner_eq_sum_support_right (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P Q = ∑ α ∈ Q.support, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α :=
  fockInner_eq_sum_right P Q Q.support (Finset.Subset.refl _)
end FockRaiseLowInner
end
end

set_option autoImplicit false
noncomputable section
open FockRaiseLowInner
open MvPolynomial FockH1Action
variable {σ : Type*}
namespace FockRaiseLowInner
theorem _root_.solution (P Q : MvPolynomial σ ℂ) :
    fockInner (-P) Q = - fockInner P Q := by
  rw [fockInner_eq_sum_support_right (-P) Q, fockInner_eq_sum_support_right P Q,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_neg, map_neg]
  ring
end FockRaiseLowInner
