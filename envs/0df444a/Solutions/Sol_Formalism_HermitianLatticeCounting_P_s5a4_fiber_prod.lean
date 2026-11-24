-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5a4_fiber_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:47.654873+00:00
-- url     : https://prove2.me/submissions/7ed6d305-b2a8-4405-9bdf-91e790d4e656

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
theorem _root_.solution {α : Type} {n : ℕ} (g : α → Fin n) (f : α → ℕ) (s : Multiset α) :
    ∏ i, ((s.filter (fun a => g a = i)).map f).prod = (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have : ∀ i, (((a ::ₘ s).filter (fun a => g a = i)).map f).prod =
        (if g a = i then f a else 1) * ((s.filter (fun a => g a = i)).map f).prod := by
      intro i
      by_cases h : g a = i
      · rw [Multiset.filter_cons_of_pos (p := fun a => g a = i) s h, Multiset.map_cons, Multiset.prod_cons, if_pos h]
      · rw [Multiset.filter_cons_of_neg (p := fun a => g a = i) s h, if_neg h, one_mul]
    simp only [this, Finset.prod_mul_distrib, ih, Finset.prod_ite_eq, Finset.mem_univ, if_true,
      Multiset.map_cons, Multiset.prod_cons]
end Formalism.HermitianLatticeCounting.P
