-- Prove2me | solution 1 for FockRaiseLowGrade.eq_zero_of_hc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:17.869987+00:00
-- url     : https://prove2.me/submissions/252c8353-13da-49cc-b9e2-fe507ded791a

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
theorem _root_.solution (x : MvPolynomial σ ℂ) (h : ∀ e, homogeneousComponent e x = 0) :
    x = 0 := by
  calc x = ∑ i ∈ Finset.range (x.totalDegree + 1), homogeneousComponent i x :=
        (sum_homogeneousComponent x).symm
    _ = 0 := Finset.sum_eq_zero (fun i _ => h i)
end FockRaiseLowGrade
