-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.lattice_linear_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:04.850583+00:00
-- url     : https://prove2.me/submissions/84ab289c-6a5a-4f0b-830a-b9be83655e8f

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_PLL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_PplusL_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution : PLLin := by
  intro p _ N r _ D L j jp
  exact ⟨⟨cmPLL p D L j jp, cm_PLL_apply L j jp⟩, ⟨cmPplusL p D jp, cm_PplusL_apply jp⟩⟩
end Formalism.InvariantFactorPaths.KP.LL
