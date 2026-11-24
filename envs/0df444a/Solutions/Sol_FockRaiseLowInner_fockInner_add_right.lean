-- Prove2me | solution 1 for FockRaiseLowInner.fockInner_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:51.419124+00:00
-- url     : https://prove2.me/submissions/94b5d427-d51b-4640-832a-bcdaa0fed50f

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
theorem _root_.solution (P Q₁ Q₂ : MvPolynomial σ ℂ) :
    fockInner P (Q₁ + Q₂) = fockInner P Q₁ + fockInner P Q₂ := by
  rw [fockInner_eq_support P (Q₁ + Q₂), fockInner_eq_support P Q₁,
    fockInner_eq_support P Q₂, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_add]
  ring
end FockRaiseLowInner
