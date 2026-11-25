-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.FG_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:45:53.553599+00:00
-- url     : https://prove2.me/submissions/1ce9211a-25a5-4007-ac52-73679ce5eaac

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
theorem _root_.solution {a : Matrix.GeneralLinearGroup (Fin n) K} (ha : a ∈ FG n K n) : a = 1 := by
  have h0 := (Bd.mono (by omega) ha : Bd n _).eq_zero
  apply Units.ext
  rw [Units.val_one]
  exact sub_eq_zero.mp h0
end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
