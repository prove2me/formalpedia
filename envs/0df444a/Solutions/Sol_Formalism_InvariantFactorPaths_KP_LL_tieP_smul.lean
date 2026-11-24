-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.tieP_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:15.950346+00:00
-- url     : https://prove2.me/submissions/9d12fe51-3ea3-4f38-bd49-d6a5c21d370f

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PstScalMem

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
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) (c : k)
    (y : MvPolynomial σ k) : tieP w e zv sv o n z (c • y) = c • tieP w e zv sv o n z y := by
  unfold tieP
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [mul_smul_comm, map_smul, map_smul, smul_comm]
end Formalism.InvariantFactorPaths.KP.LL
