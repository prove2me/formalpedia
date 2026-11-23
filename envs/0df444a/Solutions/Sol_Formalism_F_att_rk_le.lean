-- Prove2me | solution 1 for Formalism.F.att_rk_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:34.825814+00:00
-- url     : https://prove2.me/submissions/c2665e83-c197-48d7-b75c-291f2ae9672d

import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_MuMaxAttained

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.F
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.F
theorem _root_.solution {L N : Submodule ℤ E} [DiscreteTopology L] (h : N ≤ L) : rk N ≤ rk L :=
  LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion h) (Submodule.inclusion_injective h)
end Formalism.F
