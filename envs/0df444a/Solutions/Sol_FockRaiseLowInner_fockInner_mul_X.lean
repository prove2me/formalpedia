-- Prove2me | solution 1 for FockRaiseLowInner.fockInner_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:40:56.162798+00:00
-- url     : https://prove2.me/submissions/cdffaf3f-de78-4370-aa2f-26e94c1a19c6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Theorems.Thm_FockRaiseLowInner_fockInner_swap
import Theorems.Thm_FockRaiseLowInner_fockInner_X_mul

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
theorem _root_.solution (l : σ) (P Q : MvPolynomial σ ℂ) :
    fockInner P (X l * Q) = fockInner (pderiv l P) Q := by
  rw [fockInner_swap (X l * Q) P, fockInner_X_mul, ← fockInner_swap]
end FockRaiseLowInner
