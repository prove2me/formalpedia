-- Prove2me | solution 1 for FockRL.linePos_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:40.879156+00:00
-- url     : https://prove2.me/submissions/11b61ffc-5266-4385-8f32-d6d7131535c5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_KroneckerMapOneRightNeZero

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
theorem _root_.solution {p q r s : ℕ} (a : FockH1Action.Ix p q) (b b' : FockH1Action.Ix r s) :
    FockH1Action.linePos ((a, b) : FockH1Action.Ln p q r s) = FockH1Action.linePos ((a, b') : FockH1Action.Ln p q r s) ↔
      FockH1Action.sameBlock b b' := by
  rcases a with a | a <;> rcases b with b | b <;> rcases b' with b' | b' <;>
    simp [FockH1Action.linePos, FockH1Action.sameBlock]
end FockRL
