-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.unitsMap_five_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:05:26.233279+00:00
-- url     : https://prove2.me/submissions/64df2f78-2467-40a0-bc6f-fc4ef554a65b

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
open Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
namespace Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
theorem _root_.solution (n : ℕ) (h : 4 ∣ 2 ^ n) : ZMod.unitsMap h (u5 n) = 1 := by
  apply Units.ext
  first
    | (rw [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, MonoidHom.coe_coe, map_natCast]
       decide)
    | (simp only [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, MonoidHom.coe_coe, map_natCast]
       decide)
    | (rw [ZMod.unitsMap_def, Units.coe_map, u5, ZMod.coe_unitOfCoprime, ZMod.castHom_apply, ZMod.cast_natCast h]
       decide)
end Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
