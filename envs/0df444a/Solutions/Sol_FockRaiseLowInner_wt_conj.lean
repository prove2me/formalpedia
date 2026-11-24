-- Prove2me | solution 1 for FockRaiseLowInner.wt_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:19.367591+00:00
-- url     : https://prove2.me/submissions/ea8888b8-72df-47bb-8662-f74983b7c423

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight

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
theorem _root_.solution (α : σ →₀ ℕ) : (starRingEnd ℂ) (wt α) = wt α := by
  unfold wt Finsupp.prod
  rw [map_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact map_natCast _ _
end FockRaiseLowInner
