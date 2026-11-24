-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.mod_four_character_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:37:27.256176+00:00
-- url     : https://prove2.me/submissions/65f4a37d-29c0-4c6d-ad95-1a89a63a3968

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_unitsMap_neg_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Subgroup
namespace Formalism.TwoAdicCyclotomicDecomposition
namespace ModelEmbedding
end ModelEmbedding
open ModelEmbedding
namespace ModelEmbedding
end ModelEmbedding
open ModelEmbedding
namespace ModelEmbedding
private lemma chi4_unitsMap_neg_one_eq_neg_one {N : ℕ} (h : 4 ∣ N) :
    ZMod.χ₄.toUnitHom (ZMod.unitsMap h (-1 : (ZMod N)ˣ)) = -1 := by
  rw [unitsMap_neg_one]
  apply Units.ext
  rw [MulChar.coe_toUnitHom]
  first | rfl | decide | simp | (simp; decide)
end ModelEmbedding
open ModelEmbedding
end Formalism.TwoAdicCyclotomicDecomposition
end

set_option autoImplicit false
open Subgroup
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open ModelEmbedding
open ModelEmbedding
open Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
namespace Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
theorem _root_.solution (k : ℕ) : chi4 k (-1) = -1 := by
  rw [chi4, MonoidHom.comp_apply]
  exact chi4_unitsMap_neg_one_eq_neg_one _
end Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
