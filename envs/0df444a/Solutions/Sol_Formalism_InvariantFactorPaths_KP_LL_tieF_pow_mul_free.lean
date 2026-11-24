-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.tieF_pow_mul_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:15.94261+00:00
-- url     : https://prove2.me/submissions/1ab0c033-245f-4009-bc0f-a19e89e88338

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ScalSum
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_TieFPowMulFree
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
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ)
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (q f : MvPolynomial σ k) (hw : ∀ c, pderiv (w c) q = 0)
    (he : ∀ c, pderiv (e c) q = 0) (m : ℕ) :
    (tieF w e ^ m) (q * f) = q * (tieF w e ^ m) f := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ']
    show tieF w e ((tieF w e ^ m) (q * f)) = q * tieF w e ((tieF w e ^ m) f)
    rw [ih, tieF_mul_free w e q _ hw he]
end Formalism.InvariantFactorPaths.KP.LL
