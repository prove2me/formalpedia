-- Prove2me | solution 1 for Formalism.F.sub_mem_of_starProjection_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:21.059663+00:00
-- url     : https://prove2.me/submissions/c18b19c1-5af6-4db9-a1cb-b1c28520d5f1

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
theorem _root_.solution (W : Submodule ℝ E) {x z : E}
    (h : Wᗮ.starProjection x = Wᗮ.starProjection z) : x - z ∈ W := by
  have h0 : Wᗮ.starProjection (x - z) = 0 := by rw [map_sub, h, sub_self]
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal] at h0
  exact h0
end Formalism.F
