-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.sp_wU_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:04.776205+00:00
-- url     : https://prove2.me/submissions/ebdf0953-74a1-45e6-aa63-a0c690354073

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepPlus

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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] {D : BlockData N}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution : Function.Injective (wU (r := r) D) := by
  intro c d h
  simp only [wU, Sum.inl.injEq, Prod.mk.injEq] at h
  exact h.2
end Formalism.InvariantFactorPaths.KP.LL
