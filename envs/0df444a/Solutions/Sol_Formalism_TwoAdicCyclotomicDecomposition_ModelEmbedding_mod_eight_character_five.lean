-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.mod_eight_character_five
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:37:24.979942+00:00
-- url     : https://prove2.me/submissions/94230e70-7442-41c9-969c-d243e9afe464

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
private lemma chi8_unitsMap_u5_eq_neg_one (k : ℕ) (h : 8 ∣ 2 ^ (k + 3)) :
    ZMod.χ₈.toUnitHom (ZMod.unitsMap h (u5 (k + 3))) = -1 := by
  apply Units.ext
  rw [MulChar.coe_toUnitHom]
  have h5 : ((ZMod.unitsMap h (u5 (k + 3)) : (ZMod 8)ˣ) : ZMod 8) = 5 := by
    first
      | (rw [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, MonoidHom.coe_coe, map_natCast]; rfl)
      | (simp only [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, MonoidHom.coe_coe, map_natCast]; rfl)
      | (rw [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, ZMod.castHom_apply, ZMod.cast_natCast h]; rfl)
  rw [h5]
  first | rfl | decide
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
theorem _root_.solution (k : ℕ) : chi8 k (u5 (k + 3)) = -1 := by
  rw [chi8, MonoidHom.comp_apply]
  exact chi8_unitsMap_u5_eq_neg_one k _
end Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
