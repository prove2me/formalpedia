-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.cm_tiePL_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:42:58.743128+00:00
-- url     : https://prove2.me/submissions/e6222b18-9a4b-4d33-862b-a442773abd84

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
variable {p : ℕ} [Fact p.Prime] {σ : Type} {r : ℕ}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) (x : MvPolynomial σ ℚ_[p]) :
    cmTiePL w e zv sv o n z x = tieP w e zv sv o n z x := by
  simp only [cmTiePL, tieP, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    LinearMap.mulLeft_apply]
end Formalism.InvariantFactorPaths.KP.LL
