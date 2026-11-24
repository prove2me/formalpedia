-- Prove2me | solution 1 for FockRaiseLowInner.fockInner_neg_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:51.842569+00:00
-- url     : https://prove2.me/submissions/cde0defd-b6eb-4020-9e8f-d12886328043

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Theorems.Thm_FockRaiseLowInner_fockInner_eq_support

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
theorem _root_.solution (P Q : MvPolynomial σ ℂ) :
    fockInner P (-Q) = - fockInner P Q := by
  rw [fockInner_eq_support P (-Q), fockInner_eq_support P Q, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_neg]
  ring
end FockRaiseLowInner
