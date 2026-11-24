-- Prove2me | solution 1 for FockRaiseLowInner.fockInner_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:51.393459+00:00
-- url     : https://prove2.me/submissions/e6dc9c33-f346-46d1-8b3e-26bb5546c716

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
theorem _root_.solution (P Q : MvPolynomial σ ℂ) (c : ℂ) :
    fockInner P (c • Q) = c * fockInner P Q := by
  rw [fockInner_eq_support P (c • Q), fockInner_eq_support P Q, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_smul, smul_eq_mul]
  ring
end FockRaiseLowInner
