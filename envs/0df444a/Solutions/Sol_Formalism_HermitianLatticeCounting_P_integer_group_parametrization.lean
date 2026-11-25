-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.integer_group_parametrization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:05:23.259332+00:00
-- url     : https://prove2.me/submissions/efd7efa0-bef8-474c-b2b3-6dc8387cd184

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ZZgParam := by
  intro E _ _ g p
  constructor
  · rintro ⟨⟨y1, h1⟩, ⟨y2, h2⟩, w, hw⟩
    refine ⟨y2, w, 0, ?_⟩
    ext
    · simp only; rw [← hw, h2]; ring
    · simp [h2]
  · rintro ⟨c, a₁, a₂, rfl⟩
    refine ⟨⟨-c + g * a₁, by simp⟩, ⟨c + g * a₂, by simp⟩, a₁ + a₂, ?_⟩
    push_cast; ring
end Formalism.HermitianLatticeCounting.P
