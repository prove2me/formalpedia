-- Prove2me | solution 1 for Formalism.F.finite_mem_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:39:48.222271+00:00
-- url     : https://prove2.me/submissions/35c56077-bd18-4c80-b50c-2b4707ec7542

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolPos
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SaturationProperties
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_MuMaxAttained
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_FiniteSaturated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.F
theorem _root_.solution (L : Submodule ℤ E) [hL : DiscreteTopology L] (C : ℝ) :
    {v : E | v ∈ L ∧ ‖v‖ ≤ C}.Finite := by
  have hD : DiscreteTopology (L.toAddSubgroup) := hL
  have hcl : IsClosed (L : Set E) := AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)
  have hs : IsDiscrete (L : Set E) := isDiscrete_iff_discreteTopology.mpr hL
  refine (Metric.finite_isBounded_inter_isClosed hs (Metric.isBounded_closedBall (x := (0 : E)) (r := C))
    hcl).subset ?_
  intro v hv
  exact ⟨mem_closedBall_zero_iff.mpr hv.2, hv.1⟩
end Formalism.F
