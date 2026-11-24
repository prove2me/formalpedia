-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.card_QQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:37:23.699798+00:00
-- url     : https://prove2.me/submissions/80c8e5ca-daf0-4777-ae97-7087d18c437f

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Subgroup
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open ModelEmbedding
open ModelEmbedding
open Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
namespace Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
theorem _root_.solution (n : ℕ) :
    Nat.card ((GalL n ⧸ zpowers (JJ n)) ⧸
      (powMonoidHom 2 : (GalL n ⧸ zpowers (JJ n)) →* _).range) = (KK n).index := by
  rw [KK, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
  rfl
end Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
