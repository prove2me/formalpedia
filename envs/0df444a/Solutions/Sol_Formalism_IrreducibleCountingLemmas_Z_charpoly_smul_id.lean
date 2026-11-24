-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.charpoly_smul_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:52:48.256609+00:00
-- url     : https://prove2.me/submissions/af2fd1c3-00fa-4cf1-8b88-9f048063a672

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Topology
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution {K B : Type} [Field K] [AddCommGroup B] [Module K B]
    [FiniteDimensional K B] (c : K) :
    (c • (LinearMap.id : B →ₗ[K] B)).charpoly = (X - C c) ^ Module.finrank K B := by
  rw [LinearMap.charpoly_def, map_smul, LinearMap.toMatrix_id, Matrix.smul_one_eq_diagonal,
    Matrix.charpoly_diagonal, Finset.prod_const, Finset.card_univ,
    Module.finrank_eq_card_chooseBasisIndex]
end Formalism.IrreducibleCountingLemmas.Z
