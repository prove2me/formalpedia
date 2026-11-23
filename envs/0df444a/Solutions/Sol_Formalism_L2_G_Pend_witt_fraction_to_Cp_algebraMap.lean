-- Prove2me | solution 1 for Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:38.474812+00:00
-- url     : https://prove2.me/submissions/ffd4c0fd-8df0-4016-9778-2ae9f66c57b7

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
theorem _root_.solution (x : WW p) : k0ToC p (algebraMap (WW p) (K0 p) x) = wToC p x :=
  IsFractionRing.lift_algebraMap (wToC_injective p) x
end Formalism.L2.G.Pend
