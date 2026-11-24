-- Prove2me | solution 1 for FockRaiseLowInner.fockInner_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:11.20509+00:00
-- url     : https://prove2.me/submissions/b2e0c619-f534-4133-8336-113829813014

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Theorems.Thm_FockRaiseLowInner_fockInner_add_right
import Theorems.Thm_FockRaiseLowInner_fockInner_neg_right

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
    fockInner P (Q₁ - Q₂) = fockInner P Q₁ - fockInner P Q₂ := by
  rw [sub_eq_add_neg, fockInner_add_right, fockInner_neg_right, ← sub_eq_add_neg]
end FockRaiseLowInner
