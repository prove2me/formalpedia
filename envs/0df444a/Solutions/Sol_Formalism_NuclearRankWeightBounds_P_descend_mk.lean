-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.descend_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:23:46.071349+00:00
-- url     : https://prove2.me/submissions/7728da47-5275-48f2-a771-ff11d520dd82

import Definitions.Def_Formalism_LogSumExpBounds_StatementC
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_KappaModulusHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Matrix Formalism.NuclearRankWeightBounds.C
variable {RR : Type*} {K : Type*} [CommRing RR] [CommRing K] [Algebra RR K]
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution {k : ℕ} (Z : Matrix (Fin k) (Fin k) RR) (r : Fin k → K)
    (hZ : LinearMap.range Z.mulVecLin ≤ LinearMap.ker (rowInvMod K Z r)) (v : Fin k → RR) :
    descend K Z r (Submodule.Quotient.mk v) = rowInvMod K Z r v := by
  classical
  unfold descend
  rw [dif_pos hZ]
  rfl
end Formalism.NuclearRankWeightBounds.P
