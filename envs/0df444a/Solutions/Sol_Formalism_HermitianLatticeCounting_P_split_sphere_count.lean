-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.split_sphere_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:02:26.697379+00:00
-- url     : https://prove2.me/submissions/fcd8e281-9ae6-468d-8bbc-5f8967c82365

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_fiber_card

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
theorem _root_.solution : SplitSphereCount := by
  intro K _ _ M
  classical
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun (a b : Fin (M + 1) → K) => ∑ i, a i * b i = 1)), Nat.card_sigma]
  have h0 : Nat.card {b : Fin (M + 1) → K // ∑ i, (0 : Fin (M + 1) → K) i * b i = 1} = 0 := by
    have : IsEmpty {b : Fin (M + 1) → K // ∑ i, (0 : Fin (M + 1) → K) i * b i = 1} :=
      ⟨fun b => by have := b.2; simp at this⟩
    exact Nat.card_of_isEmpty
  rw [← Finset.sum_erase (f := fun a : Fin (M + 1) → K => Nat.card {b : Fin (M + 1) → K // ∑ i, a i * b i = 1}) Finset.univ h0]
  rw [Finset.sum_congr rfl (fun x hx => s5a4_fiber_card M x (Finset.ne_of_mem_erase hx) 1)]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, smul_eq_mul, mul_comm]
end Formalism.HermitianLatticeCounting.P
