-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.st_wv_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:15.727363+00:00
-- url     : https://prove2.me/submissions/b14c59fc-54b8-48f1-834d-734d2c00a513

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepTie

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
variable {D}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (kk : Fin D.T.t) : Function.Injective (wv (r := r) D kk) := by
  intro c d h
  exact (Prod.mk.inj (Sum.inl.inj h)).2
end Formalism.InvariantFactorPaths.KP.LL
