-- Prove2me | solution 1 for Formalism.L2.Pj.CompSplitPfD.cspD_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:14:43.028603+00:00
-- url     : https://prove2.me/submissions/a3954c52-3dd7-4d77-b44c-434f78de8f39

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompFin
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfC
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.CompSplitPfD
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Topology
namespace Formalism.L2.Pj.CompSplitPfD
theorem _root_.solution {X : Type} [TopologicalSpace X] [T0Space X] {W : Set X}
    (hW : W ∈ irreducibleComponents X) {η : X} (hη : IsGenericPoint η W) (z : X) (hz : z ⤳ η) : z = η := by
  have hWc : closure ({η} : Set X) = W := hη
  have h1 : closure ({η} : Set X) ⊆ closure {z} := specializes_iff_closure_subset.mp hz
  have hirr : IsIrreducible (closure ({z} : Set X)) := isIrreducible_singleton.closure
  have h2 : closure ({z} : Set X) ⊆ W := hW.2 hirr (hWc ▸ h1)
  have h3 : closure ({z} : Set X) = closure {η} := le_antisymm (hWc ▸ h2) h1
  exact (inseparable_iff_closure_eq.mpr h3).eq
end Formalism.L2.Pj.CompSplitPfD
