-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.tower_group_foundations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:20:11.636059+00:00
-- url     : https://prove2.me/submissions/61ee0eeb-d2f3-4992-99ce-8237602b9cc3

import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OrderOfThreeUnitsTwoPow
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NegOneNeOneUnitsZmodFour
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Groups
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_FinalGroup
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
    UnitsTwoPow ∧ QuotCyclic ∧ TwoAdicOrder ∧ TwoAdicVal ∧ DecompModel ∧ GmRank ∧ GensModel ∧
    GamEModel ∧ GGModel ∧ CentralExtAbelian ∧ CommGen ∧ RankBound ∧
    NormalOrderTwoCentral ∧ TwistVal ∧ CoinvLength ∧ PGroupGen ∧ GenusModel ∧ GenusAbelian :=
  ⟨unitsTwoPow, quotCyclic, twoAdicOrder, twoAdicVal, decompModel, gmRank, gensModel,
   gamEModel, ggModel, centralExtAbelian, commGen, rankBound,
   normalOrderTwoCentral, twistVal, coinvLength, pGroupGen, genusModel, genusAbelian⟩
end Formalism.TwoAdicCyclotomicDecomposition
