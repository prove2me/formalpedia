-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.exampleZ_not_mem_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:54.016136+00:00
-- url     : https://prove2.me/submissions/8323092a-6de1-402c-a6fe-815b9fb74292

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
theorem _root_.solution {s : ℤ} (hs : Odd s) : s ∉ Ideal.span {(2 : ℤ)} := by
  rw [Ideal.mem_span_singleton, ← even_iff_two_dvd, Int.not_even_iff_odd]
  exact hs
end Formalism.HermitianLatticesTheory
