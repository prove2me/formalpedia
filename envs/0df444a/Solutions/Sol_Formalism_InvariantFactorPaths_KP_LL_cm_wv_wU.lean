-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.cm_wv_wU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:47.434193+00:00
-- url     : https://prove2.me/submissions/eaf5ef00-71a9-4398-9141-e6ea74d32e77

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_finPos_pos_val
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_pos_lt_u


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
theorem _root_.solution (hB : D.BlockOK) (i : Fin D.T.t) (c d : Fin r) : wv D i d ≠ wU D c := by
  intro h'
  simp only [wv, wU, Sum.inl.injEq, Prod.mk.injEq] at h'
  have := congrArg Fin.val h'.1
  rw [finPos_pos_val hB, Fin.val_castSucc] at this
  have := pos_lt_u hB i
  omega
end Formalism.InvariantFactorPaths.KP.LL
