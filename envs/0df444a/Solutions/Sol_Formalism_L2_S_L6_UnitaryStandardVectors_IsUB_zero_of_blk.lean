-- Prove2me | solution 1 for Formalism.L2.S.L6.UnitaryStandardVectors.IsUB.zero_of_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:17:46.398384+00:00
-- url     : https://prove2.me/submissions/4006a282-cab3-4a47-a8e4-830054d3a020

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ZeroOfBlk

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
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.L6 Formalism.L2.S.L6.UnitaryStandardVectors
variable {m : ℕ}
namespace Formalism.L2.S.L6.UnitaryStandardVectors
namespace IsUB
theorem _root_.solution {blk : Fin m → ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (h : IsUB blk C) {i j : Fin m}
    (hij : blk i ≠ blk j) : C i j = 0 := by
  by_contra hne
  exact hij (h.2 i j hne).2
end IsUB
end Formalism.L2.S.L6.UnitaryStandardVectors
