-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.tieF_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:15.934384+00:00
-- url     : https://prove2.me/submissions/e51823e0-52c4-4a77-b6e2-e014fec16900

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_chainEmb_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_ev_chain
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_wv_chain
import Theorems.Thm_P2M_Formalism_GM_tieF_apply__aa4421b36bb1


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
open MvPolynomial Finset Formalism.GM.M Formalism.GM.M.PhiIntegrality
variable {p : ℕ} [Fact p.Prime]
variable {N r : ℕ} [NeZero r] {D : BlockData N}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (hB : D.BlockOK) (i : Fin D.T.t) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (g : MvPolynomial (BVar N r D.T.t) ℚ_[p]) (hw : ∀ c, pderiv (wv D i c) g = 0)
    (he : ∀ c, pderiv (ev D i c) g = 0) :
    tieF (wv D i) (ev D i) (rename (chainEmb N r D.T.t) y * g) =
      rename (chainEmb N r D.T.t)
        (tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) y) * g := by
  rw [tieF_apply', tieF_apply', map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [pderiv_mul, he c, mul_zero, add_zero, ev_chain hB, pderiv_rename chainEmb_inj, pderiv_mul, hw c,
    mul_zero, add_zero, wv_chain hB, pderiv_rename chainEmb_inj]
end Formalism.InvariantFactorPaths.KP.LL
