-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.FG_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:45:55.780874+00:00
-- url     : https://prove2.me/submissions/b00b788b-5076-4a95-8562-cc611c1c682c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_InvSubOneBd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RelativeIndexFlags Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
variable {n : ℕ} {K : Type*} [Field K]
namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
theorem _root_.solution (k : ℕ) : FG n K (k + 1) ≤ FG n K k := fun _ ha => Bd.mono (by omega) ha
end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
