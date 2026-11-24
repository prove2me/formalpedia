-- Prove2me | solution 1 for FockRaiseLowGrade.hc_hc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:39.275622+00:00
-- url     : https://prove2.me/submissions/ea9e8023-c40d-42c9-82f8-38715d85b6d3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_RaisingLoweringSplit

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
theorem _root_.solution (m n : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent m (homogeneousComponent n P) =
      if m = n then homogeneousComponent n P else 0 := by
  classical
  rw [homogeneousComponent_of_mem (homogeneousComponent_mem n P)]
end FockRaiseLowGrade
