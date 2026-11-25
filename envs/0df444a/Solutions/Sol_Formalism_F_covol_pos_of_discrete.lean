-- Prove2me | solution 1 for Formalism.F.covol_pos_of_discrete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:55:26.642801+00:00
-- url     : https://prove2.me/submissions/b8af383f-a37d-49cc-88c2-a0757945748e

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeInequality
import Theorems.Thm_Formalism_F_det_gram_basis_pos

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
universe u v
namespace Formalism.F
theorem _root_.solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    0 < covol L := by
  classical
  rw [covol, dif_pos (inferInstance : DiscreteTopology L)]
  exact Real.sqrt_pos.mpr (det_gram_basis_pos L _)
end Formalism.F
