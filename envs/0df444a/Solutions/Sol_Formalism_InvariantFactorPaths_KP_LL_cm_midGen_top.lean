-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.cm_midGen_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:04.915974+00:00
-- url     : https://prove2.me/submissions/bed977f3-418a-4058-b885-d6a857236cc2

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds

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
theorem _root_.solution (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    midGen p D D.T.t j jp x = (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
      (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) * X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus *
      x := by
  unfold midGen
  rw [List.drop_eq_nil_of_le (by simp), Finset.filter_true_of_mem (fun i _ => i.2)]
  rfl
end Formalism.InvariantFactorPaths.KP.LL
