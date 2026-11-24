-- Prove2me | solution 1 for FockRL.conjR_apply_of_not
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:16.929968+00:00
-- url     : https://prove2.me/submissions/b457dc06-6f3f-4c81-be3e-348f11409fb7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_KroneckerMapOneRightNeZero
import Theorems.Thm_FockRL_conjR_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open FockRL
namespace FockRL
theorem _root_.solution {p q : ℕ} (Z : FockH1Action.Mat p q) {a b : FockH1Action.Ix p q}
    (h : ¬ FockH1Action.sameBlock a b) : FockH1Action.conjR Z a b = (starRingEnd ℂ) (Z b a) := by
  rw [conjR_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp_all [FockH1Action.sameBlock, jsgn]
end FockRL
