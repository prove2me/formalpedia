-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.genusModel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:24:36.806943+00:00
-- url     : https://prove2.me/submissions/b68e5fdd-48c5-4b1e-ab7a-6b907fc41f7d

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_neg_one_ne_one_int

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
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : GenusModel := by
  intro n
  refine ⟨?_, ?_, Subgroup.mem_zpowers _, Subgroup.mem_zpowers _, ?_⟩
  · simp [JJ]
  · rw [I2, MonoidHom.mem_ker]; rfl
  · intro h
    exact neg_one_ne_one_int (congrArg (fun g : GalL n => g.2.1) h)
end Formalism.TwoAdicCyclotomicDecomposition
