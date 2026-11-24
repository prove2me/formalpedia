-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.st_notin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:50.06287+00:00
-- url     : https://prove2.me/submissions/872c5622-9558-4a0c-b5ac-c40704a8e7a9

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepTie
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_st_drop

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
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (t k : ℕ) (hk : k < t) : (⟨k, hk⟩ : Fin t) ∉ (List.finRange t).drop (k + 1) := by
  have h := List.Nodup.sublist (List.drop_sublist k (List.finRange t)) (List.nodup_finRange t)
  rw [st_drop t k hk] at h
  exact (List.nodup_cons.1 h).1
end Formalism.InvariantFactorPaths.KP.LL
