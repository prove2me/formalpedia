-- Prove2me | solution 1 for Formalism.F.discreteTopology_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T16:56:29.171351+00:00
-- url     : https://prove2.me/submissions/1cb98c57-cc96-4015-8c23-fa0d8b0b5f4a

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.F
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.F
theorem _root_.solution {L N : Submodule ℤ E} (h : N ≤ L) [hL : DiscreteTopology L] :
    DiscreteTopology N :=
  DiscreteTopology.of_continuous_injective (f := Submodule.inclusion h)
    (continuous_subtype_val.subtype_mk _) (Submodule.inclusion_injective h)
end Formalism.F
