-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.sub_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:01:44.521448+00:00
-- url     : https://prove2.me/submissions/f1d4b26d-7803-4830-83ba-c43156eac29a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_InvSubOneBd
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_FiltRelIndex
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexUnipotentConjSymm
import Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_FG_comm


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
theorem _root_.solution (hLF : L ≤ FG n K 0) (k : ℕ) (a b : L) (hb : b ∈ (FG n K k).subgroupOf L) :
    a * b * a⁻¹ * b⁻¹ ∈ (FG n K (k + 1)).subgroupOf L := by
  rw [Subgroup.mem_subgroupOf] at hb ⊢
  have h := FG_comm k (a : Matrix.GeneralLinearGroup (Fin n) K) b (hLF a.2) hb
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
