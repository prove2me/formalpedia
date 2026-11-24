-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.exampleZ_two_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:54.788973+00:00
-- url     : https://prove2.me/submissions/67f664a5-6bbf-44d8-8655-1e45aa7e08b0

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ExampleZ
import Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_mem_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : Submodule.span ℤ {(2 : ℚ)} ≤ (1 : Submodule ℤ ℚ) := by
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact (exampleZ_mem_one 2).mpr ⟨2, by norm_num⟩
end Formalism.HermitianLatticesTheory
