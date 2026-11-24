-- Prove2me | solution 1 for FockRaiseLowInner.fockInner_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:24.990327+00:00
-- url     : https://prove2.me/submissions/e64d0d78-b449-43a6-88c3-aa5f1562bcad

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
theorem _root_.solution (P₁ P₂ Q : MvPolynomial σ ℂ) :
    fockInner (P₁ + P₂) Q = fockInner P₁ Q + fockInner P₂ Q := by
  rw [fockInner_eq_sum_support_right (P₁ + P₂) Q, fockInner_eq_sum_support_right P₁ Q,
    fockInner_eq_sum_support_right P₂ Q, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_add, map_add]
  ring
end FockRaiseLowInner
