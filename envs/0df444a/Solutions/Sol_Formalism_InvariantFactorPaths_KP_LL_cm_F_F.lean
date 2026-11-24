-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.cm_F_F
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:51.889831+00:00
-- url     : https://prove2.me/submissions/7693acae-f6e5-44f2-8157-1d3b6faab7ec

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_commute_pderiv


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
variable {p : ℕ} [Fact p.Prime] {σ : Type} {r : ℕ}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution {r' : ℕ} (w' e' : Fin r' → σ) (w e : Fin r → σ) :
    Commute (tieF (k := ℚ_[p]) w' e') (tieF w e) := by
  unfold tieF
  refine Commute.sum_left _ _ _ (fun c _ => Commute.sum_right _ _ _ (fun d _ => ?_))
  simp only [← Module.End.mul_eq_comp]
  refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_) <;>
    exact PhiIntegrality.commute_pderiv _ _
end Formalism.InvariantFactorPaths.KP.LL
