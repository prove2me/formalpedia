-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.third_reduction_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:01:30.685794+00:00
-- url     : https://prove2.me/submissions/63965370-754d-4b7b-bebe-7a757e927659

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_charpolyRev_map_alt
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_same_residue_holds
import Theorems.Thm_Formalism_ResultantValuation_AdjugateJacobi_key


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
theorem _root_.solution : ResidueCharpolyEq := by
  intro O _ _ X' _ T hT G n r hr x y g
  have h1 : Matrix.charpolyRev ((r x g).map (IsLocalRing.residue O)) =
      Matrix.charpolyRev ((r y g).map (IsLocalRing.residue O)) := by
    rw [charpolyRev_map_alt, charpolyRev_map_alt]
    ext j
    rw [coeff_map, coeff_map]
    exact same_residue_holds O X' T hT _ (hr g j) x y
  refine ⟨h1, ?_⟩
  have key : ∀ M : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O),
      M.charpoly = (Matrix.charpolyRev M).reflect n := by
    intro M
    rw [← Matrix.reverse_charpoly, Polynomial.reverse, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin, reflect_reflect]
  rw [key, key, h1]
end Formalism.IrreducibleCountingLemmas.Z
