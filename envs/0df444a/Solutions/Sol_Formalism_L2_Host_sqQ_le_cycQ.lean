-- Prove2me | solution 1 for Formalism.L2.Host.sqQ_le_cycQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:17:28.7698+00:00
-- url     : https://prove2.me/submissions/258cade1-bc60-4723-bf39-9ee1187484ae

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_Lemmas
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Theorems.Thm_Formalism_L2_Host_gaussQb_mem
import Theorems.Thm_Formalism_L2_Host_gaussQb_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IntermediateField NumberField
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable (q : ℕ) [Fact q.Prime]
variable {q}
namespace Formalism.L2.Host
theorem _root_.solution (hq : q % 4 = 3) : sqQ (-(q : ℤ)) ≤ cycQ q := by
  obtain ⟨w, hw⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Qb q
  rw [sqQ_eq (gaussQb_sq hq hw), adjoin_simple_le_iff]
  exact gaussQb_mem hw
end Formalism.L2.Host
