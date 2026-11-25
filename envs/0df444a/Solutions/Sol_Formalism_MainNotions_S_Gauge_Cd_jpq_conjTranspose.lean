-- Prove2me | solution 1 for Formalism.MainNotions.S.Gauge.Cd.jpq_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:31:01.048155+00:00
-- url     : https://prove2.me/submissions/478e119a-cf73-48d6-8207-7b7f464bbef9

import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_TraceMulConjTransposeReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Gauge Formalism.MainNotions.S.Gauge.Cd
variable {P Q : ℕ}
local notation "ι" => Fin P ⊕ Fin Q
namespace Formalism.MainNotions.S.Gauge.Cd
theorem _root_.solution : (Formalism.UG.Jpq P Q)ᴴ = Formalism.UG.Jpq P Q := by
  unfold Formalism.UG.Jpq
  rw [Matrix.fromBlocks_conjTranspose]
  simp
end Formalism.MainNotions.S.Gauge.Cd
