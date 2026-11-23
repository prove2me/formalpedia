-- Prove2me | solution 1 for Formalism.F.finiteSaturated_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:08.771389+00:00
-- url     : https://prove2.me/submissions/fde3990a-0a92-4c6a-963f-82a5541761ad

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolPos
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SaturationProperties
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_MuMaxAttained
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_FiniteSaturated
import Theorems.Thm_Formalism_F_finite_saturated_rank_le_covol_le
import Theorems.Thm_Formalism_F_degree_quotient


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
namespace Formalism.F
theorem _root_.solution (hS : ShortVector.{u}) : FiniteSaturated.{u} := by
  intro E _ _ _ L hL X
  refine (finite_saturated_rank_le_covol_le hS (rk L) L hL X).subset ?_
  rintro N ⟨hN, hX⟩
  have := (degree_quotient E L N hL hN).2.1
  exact ⟨hN, by omega, hX⟩
end Formalism.F
