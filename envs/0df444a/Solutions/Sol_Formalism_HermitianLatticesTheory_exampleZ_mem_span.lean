-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.exampleZ_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:35:38.693173+00:00
-- url     : https://prove2.me/submissions/6bb61607-44fe-472e-8dac-f2d93c58580a

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
theorem _root_.solution (c x : ℚ) : x ∈ Submodule.span ℤ {c} ↔ ∃ n : ℤ, (n : ℚ) * c = x := by
  rw [Submodule.mem_span_singleton]
  simp [zsmul_eq_mul]
end Formalism.HermitianLatticesTheory
