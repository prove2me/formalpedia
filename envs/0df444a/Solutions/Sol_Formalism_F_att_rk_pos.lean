-- Prove2me | solution 1 for Formalism.F.att_rk_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:32.040591+00:00
-- url     : https://prove2.me/submissions/5faddef8-e8cc-41f8-9312-e221e472b38f

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
theorem _root_.solution {N : Submodule ℤ E} [DiscreteTopology N] (hN : N ≠ ⊥) : 0 < rk N := by
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN
  exact Module.finrank_pos
end Formalism.F
