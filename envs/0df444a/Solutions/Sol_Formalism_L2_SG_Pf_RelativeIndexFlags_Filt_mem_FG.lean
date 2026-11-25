-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.mem_FG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:46:44.2638+00:00
-- url     : https://prove2.me/submissions/c5d95e34-9322-4eac-9407-5e05cba052a1

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
theorem _root_.solution {k : ℕ} {a : Matrix.GeneralLinearGroup (Fin n) K} :
    a ∈ FG n K k ↔ Bd (k + 1) ((a : Matrix (Fin n) (Fin n) K) - 1) := Iff.rfl
end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
