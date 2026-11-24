-- Prove2me | solution 1 for FockRaiseLowInner.fockInner_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:26.383082+00:00
-- url     : https://prove2.me/submissions/d349d8a9-ae9a-4f40-ab38-df96305a11f6

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
theorem _root_.solution (P Q : MvPolynomial σ ℂ) (c : ℂ) :
    fockInner (c • P) Q = (starRingEnd ℂ) c * fockInner P Q := by
  rw [fockInner_eq_sum_support_right (c • P) Q, fockInner_eq_sum_support_right P Q, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_smul, smul_eq_mul, map_mul]
  ring
end FockRaiseLowInner
