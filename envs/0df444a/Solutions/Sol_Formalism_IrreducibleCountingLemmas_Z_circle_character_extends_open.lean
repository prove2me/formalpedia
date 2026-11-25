-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.circle_character_extends_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:16:04.351688+00:00
-- url     : https://prove2.me/submissions/a508bcc4-be3f-4671-96a9-4484bc6773f9

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_open_subgroup_continuous
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_circle_character_extends


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
theorem _root_.solution : CircleCharExtendsOpen := by
  intro A _ _ _ U χ hU hχ
  obtain ⟨χ', h⟩ := circle_character_extends A U χ
  refine ⟨χ', open_subgroup_continuous A U χ' hU ?_, h⟩
  have : (fun u : U => χ' (u : A)) = χ := funext h
  rw [this]; exact hχ
end Formalism.IrreducibleCountingLemmas.Z
