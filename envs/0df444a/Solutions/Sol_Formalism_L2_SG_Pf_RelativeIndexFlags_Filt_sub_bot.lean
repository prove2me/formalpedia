-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.sub_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:57:36.846152+00:00
-- url     : https://prove2.me/submissions/621ae05d-4ef5-4d67-ad15-940871fe6b00

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_InvSubOneBd
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_FiltRelIndex
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexUnipotentConjSymm
import Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_FG_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RelativeIndexFlags Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
variable {n : ℕ} {K : Type*} [Field K] (L : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
theorem _root_.solution : (FG n K n).subgroupOf L = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  apply Subtype.ext
  rw [FG_eq_one hx, Subgroup.coe_one]
end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
