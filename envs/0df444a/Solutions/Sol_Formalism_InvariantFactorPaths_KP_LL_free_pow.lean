-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.free_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:48:32.430139+00:00
-- url     : https://prove2.me/submissions/047976e3-e26e-45a0-87a5-9994b56f830f

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_TieFPowMulFree
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_SmulMemOfNorm
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_free_mul

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
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution {v : σ} {a : MvPolynomial σ ℚ_[p]} (ha : pderiv v a = 0) (n : ℕ) :
    pderiv v (a ^ n) = 0 := by
  induction n with
  | zero => rw [pow_zero]; exact Derivation.map_one_eq_zero _
  | succ n ih => rw [pow_succ]; exact free_mul ih ha
end Formalism.InvariantFactorPaths.KP.LL
