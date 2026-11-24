-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.sq_mem_KK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:37:24.780321+00:00
-- url     : https://prove2.me/submissions/d77f50f0-f45d-4225-9bf6-c3edb817e737

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
theorem _root_.solution {n : ℕ} (g : GalL n) : g ^ 2 ∈ KK n := by
  rw [KK, Subgroup.mem_comap, MonoidHom.mem_range]
  exact ⟨QuotientGroup.mk' _ g, by rw [powMonoidHom_apply, map_pow]⟩
end Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
