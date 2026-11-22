-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.exampleZ_mem_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:01:15.779348+00:00
-- url     : https://prove2.me/submissions/b7ee84ee-a811-46a3-93e9-c5603010ac1f

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ExampleZ

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
theorem _root_.solution (x : ℚ) : x ∈ (1 : Submodule ℤ ℚ) ↔ ∃ n : ℤ, (n : ℚ) = x := by
  rw [Submodule.mem_one]
  simp
end Formalism.HermitianLatticesTheory
