-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5a4_card_fibers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:54.552434+00:00
-- url     : https://prove2.me/submissions/a20d02a4-433a-4299-a631-8700b60285b5

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_sum_fiber

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
theorem _root_.solution {α κ : Type} [Fintype α] [Fintype κ] (f : α → κ) :
    ∑ k, (Nat.card {a // f a = k} : ℤ) = Fintype.card α := by
  have := s5a4_sum_fiber f (fun _ => 1)
  simp at this
  rw [← this]
end Formalism.HermitianLatticeCounting.P
