-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.wU_ne_xi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:42:53.716946+00:00
-- url     : https://prove2.me/submissions/fa416058-857b-4b7b-abcf-1ec4b7a250de

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ChainEmbInj
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_BiHomPlus

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
theorem _root_.solution (c d : Fin r) : wU D c ≠ xiVar N r D.T.t d := by
  intro h
  simp only [wU, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  exact (Fin.castSucc_lt_last _).ne h.1
end Formalism.InvariantFactorPaths.KP.LL
