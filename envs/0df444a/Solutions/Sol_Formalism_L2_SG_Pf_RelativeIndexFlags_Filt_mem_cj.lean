-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.mem_cj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:45:50.452167+00:00
-- url     : https://prove2.me/submissions/8a28f5ea-0a28-4b4e-908c-76886d5a86ed

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexEqIndexOfMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RelativeIndexFlags Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
variable {G : Type*} [Group G]
namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
theorem _root_.solution (g : G) (A : Subgroup G) (y : G) : y ∈ cj g A ↔ ∃ x ∈ A, g * x * g⁻¹ = y := by
  simp [cj, Subgroup.mem_map, MulAut.conj_apply]
end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
