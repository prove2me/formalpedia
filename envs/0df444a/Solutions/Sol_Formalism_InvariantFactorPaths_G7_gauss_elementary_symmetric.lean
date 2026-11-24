-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.gauss_elementary_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:11:50.49667+00:00
-- url     : https://prove2.me/submissions/feb77d2e-93b3-4432-aabb-311e59f61091

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_GaussElementarySymmetric
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_eF_of_card_lt
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_gauss_zpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open CSym
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : GaussEsymm := by
  intro K _ Q g l hQ
  rw [gauss_zpow Q hQ g l]
  rcases le_or_gt l g with h | h
  · rw [show ((l : ℤ) * ((g : ℤ) - l)) = ((l * (g - l) : ℕ) : ℤ) by push_cast [Nat.cast_sub h]; ring,
      zpow_natCast]
  · rw [eF_of_card_lt _ _ (by simpa using h)]
    simp
end Formalism.InvariantFactorPaths.G7
