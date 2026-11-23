-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5a4_sum_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:21.264119+00:00
-- url     : https://prove2.me/submissions/8b59e6cb-ecb7-436f-a1da-f2d66b087530

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
theorem _root_.solution {α κ : Type} [Fintype α] [Fintype κ] (f : α → κ) (F : κ → ℤ) :
    ∑ a, F (f a) = ∑ k, (Nat.card {a // f a = k} : ℤ) * F k := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := f) (f := fun a => F (f a))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_congr rfl (g := fun _ => F k) (fun a ha => by rw [(Finset.mem_filter.mp ha).2]),
    Finset.sum_const, Nat.card_eq_fintype_card, Fintype.card_subtype, nsmul_eq_mul]
end Formalism.HermitianLatticeCounting.P
