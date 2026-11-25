-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.Bd.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:45:53.433744+00:00
-- url     : https://prove2.me/submissions/5ef47e4f-bad8-4a1b-8bc7-89c50251dc0f

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
namespace Bd
theorem _root_.solution {m : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : Bd m A) (hB : Bd m B) : Bd m (A - B) :=
  fun i j h => by rw [Matrix.sub_apply, hA i j h, hB i j h, sub_zero]
end Bd
end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
