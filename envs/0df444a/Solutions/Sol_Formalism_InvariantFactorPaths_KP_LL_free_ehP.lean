-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.free_ehP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:48:31.617508+00:00
-- url     : https://prove2.me/submissions/856035d3-7d43-4534-b297-52c449025de1

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_TieFPowMulFree
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_SmulMemOfNorm
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_free_X
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
theorem _root_.solution {r : ℕ} {w e : Fin r → σ} {zv sv v : σ} (h1 : zv ≠ v) (h2 : sv ≠ v) (h3 : ∀ c, w c ≠ v)
    (h4 : ∀ c, e c ≠ v) : pderiv v (ehP w e zv sv : MvPolynomial σ ℚ_[p]) = 0 := by
  unfold ehP
  rw [map_add, map_sum, free_mul (free_X h1) (free_X h2), zero_add]
  exact Finset.sum_eq_zero fun c _ => free_mul (free_X (h3 c)) (free_X (h4 c))
end Formalism.InvariantFactorPaths.KP.LL
