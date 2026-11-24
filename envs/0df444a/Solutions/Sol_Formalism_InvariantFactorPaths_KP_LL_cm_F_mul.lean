-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.cm_F_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:51.940572+00:00
-- url     : https://prove2.me/submissions/53d116a6-9797-4806-9df9-2584f33fc388

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_tieF_mul_free


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
theorem _root_.solution {r' : ℕ} (w' e' : Fin r' → σ) (q : MvPolynomial σ ℚ_[p]) (hw : ∀ c, pderiv (w' c) q = 0)
    (he : ∀ c, pderiv (e' c) q = 0) : Commute (tieF w' e') (LinearMap.mulLeft ℚ_[p] q) :=
  LinearMap.ext fun f => by
    simp only [Module.End.mul_apply, LinearMap.mulLeft_apply]
    exact tieF_mul_free w' e' q f hw he
end Formalism.InvariantFactorPaths.KP.LL
