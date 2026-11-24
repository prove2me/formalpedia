-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.towerProperties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:00:42.540864+00:00
-- url     : https://prove2.me/submissions/fc94d76f-a842-43ef-9f4b-80b76a3cbbb4

import Definitions.Def_Formalism_TameInertiaTowers_FinalGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_tower_field_foundations
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_centralExtAbelian
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_coinvLength
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_commGen
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_decompModel
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_gamEModel
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_gensModel
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_genusAbelian
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_genusModel
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ggModel
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_gmRank
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_invLength
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_normalOrderTwoCentral
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_pGroupGen
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_quotCyclic
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_rankBound
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_twistVal
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_twoAdicOrder
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_twoAdicVal
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_unitsTwoPow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution :
    (UnitsTwoPow ∧ QuotCyclic ∧ TwoAdicOrder ∧ TwoAdicVal ∧ DecompModel ∧ GmRank ∧ GensModel ∧
      GamEModel ∧ GGModel ∧ CentralExtAbelian ∧ CommGen ∧ RankBound ∧
      NormalOrderTwoCentral ∧ TwistVal ∧ CoinvLength ∧ PGroupGen ∧ GenusModel ∧ GenusAbelian) ∧
    InvLength ∧
    (LayerExists ∧ LayerGalois ∧ LayerConj ∧ LayerReal ∧ LayerDecompTwo ∧ LayerInertiaTwo ∧
      LayerEFGTwo ∧ LayerInertiaTame ∧ LayerFrob) :=
  ⟨⟨unitsTwoPow, quotCyclic, twoAdicOrder, twoAdicVal, decompModel, gmRank, gensModel, gamEModel,
      ggModel, centralExtAbelian, commGen, rankBound,
      normalOrderTwoCentral, twistVal, coinvLength, pGroupGen, genusModel, genusAbelian⟩,
    invLength, tower_field_foundations⟩
end Formalism.TwoAdicCyclotomicDecomposition
