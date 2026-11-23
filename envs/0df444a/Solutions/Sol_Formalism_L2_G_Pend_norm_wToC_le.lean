-- Prove2me | solution 1 for Formalism.L2.G.Pend.norm_wToC_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:47.124392+00:00
-- url     : https://prove2.me/submissions/5bf51b02-a395-4e61-bd1c-2ecdb65ec78c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_IsLocalRingOfComplete
import Definitions.Def_Lemmata_FirstBlockLemmaF_Imports
import Definitions.Def_Lemmata_GeneralBFactThird_Imports
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PendingLemmas_WittFractionToCpAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing Filter Topology
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Pend
variable (p : ℕ) [hp : Fact p.Prime]
attribute [local instance] algZW algQK
attribute [local instance] Formalism.L2.G.Pend.towerZQK
namespace Formalism.L2.G.Pend
theorem _root_.solution (x : WW p) : ‖wToC p x‖ ≤ 1 := norm_wFun_le p x
end Formalism.L2.G.Pend
