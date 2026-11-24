-- Prove2me | solution 1 for FockRaiseLowGrade.raisingLoweringSplit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:45.88602+00:00
-- url     : https://prove2.me/submissions/40a2d0d8-d327-41a7-b357-1513e8af66a3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_RaisingLoweringSplit
import Theorems.Thm_FockRaiseLowGrade_plus_eq
import Theorems.Thm_FockRaiseLowGrade_minus_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockRaiseLowGrade
open MvPolynomial FockH1Action
variable {σ : Type*}
namespace FockRaiseLowGrade
theorem _root_.solution : FockRL.PMSplit := by
  intro σ R L hR hL P
  exact ⟨plus_eq R L hR hL P, minus_eq R L hR hL P⟩
end FockRaiseLowGrade
