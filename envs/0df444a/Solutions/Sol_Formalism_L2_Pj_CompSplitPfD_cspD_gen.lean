-- Prove2me | solution 1 for Formalism.L2.Pj.CompSplitPfD.cspD_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:14:22.253827+00:00
-- url     : https://prove2.me/submissions/f8d343dc-75f1-44e9-b66d-06dc4b2a0c83

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
theorem _root_.solution {X : Type} [TopologicalSpace X] [QuasiSober X] {W : Set X} (hW : W ∈ irreducibleComponents X) :
    IsGenericPoint hW.1.genericPoint W := by
  have h1 := hW.1.isGenericPoint_genericPoint_closure
  rwa [(isClosed_of_mem_irreducibleComponents W hW).closure_eq] at h1
end Formalism.L2.Pj.CompSplitPfD
