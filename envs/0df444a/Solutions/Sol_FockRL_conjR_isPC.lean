-- Prove2me | solution 1 for FockRL.conjR_isPC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:17.187105+00:00
-- url     : https://prove2.me/submissions/f5f39185-9533-46b3-a1c4-067028242092

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_KroneckerMapOneRightNeZero
import Theorems.Thm_FockRL_conjR_apply
import Theorems.Thm_FockRL_sameBlock_symm

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
theorem _root_.solution {p q : ℕ} (Z : FockH1Action.Mat p q) (hZ : FockH1Action.IsPC Z) :
    FockH1Action.IsPC (FockH1Action.conjR Z) := by
  intro a b hab
  rw [conjR_apply, hZ b a (sameBlock_symm hab)]
  simp
end FockRL
