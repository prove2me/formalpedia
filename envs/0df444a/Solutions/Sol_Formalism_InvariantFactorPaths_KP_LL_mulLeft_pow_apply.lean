-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.mulLeft_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:18.594863+00:00
-- url     : https://prove2.me/submissions/a870ed66-95b0-48a2-af5d-8947da12cdfa

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ScalSum
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_TieFPowMulFree

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
theorem _root_.solution (a f : MvPolynomial σ k) (m : ℕ) :
    ((LinearMap.mulLeft k a) ^ m) f = a ^ m * f := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ' a m, mul_assoc, ← ih, pow_succ']
    show LinearMap.mulLeft k a ((LinearMap.mulLeft k a ^ m) f) = _
    rw [LinearMap.mulLeft_apply]
end Formalism.InvariantFactorPaths.KP.LL
