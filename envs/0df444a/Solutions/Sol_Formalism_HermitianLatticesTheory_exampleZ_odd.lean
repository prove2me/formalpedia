-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.exampleZ_odd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:54.294656+00:00
-- url     : https://prove2.me/submissions/819be6e7-01dc-43ef-9d0f-921555555a1a

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
theorem _root_.solution {s : ℤ} (hs : s ∉ Ideal.span {(2 : ℤ)}) : Odd s := by
  rw [Ideal.mem_span_singleton, ← even_iff_two_dvd, Int.not_even_iff_odd] at hs
  exact hs
end Formalism.HermitianLatticesTheory
