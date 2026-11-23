-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.card_fiber_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:28.657598+00:00
-- url     : https://prove2.me/submissions/ab8faa5a-6bf9-445c-b05e-23ff0098894d

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
theorem _root_.solution (W : Type*) [AddCommGroup W] [Fintype W] [DecidableEq W]
    (L : (Fin r → k) →+ W) (hL : Function.Surjective L) (w : W) :
    (univ.filter (fun f => L f = w)).card * Fintype.card W = Fintype.card k ^ r := by
  have hfib : ∀ w, (univ.filter (fun f => L f = w)).card =
      (univ.filter (fun f => L f = 0)).card := by
    intro w
    obtain ⟨f0, hf0⟩ := hL w
    refine Finset.card_nbij' (fun f => f - f0) (fun f => f + f0) ?_ ?_ ?_ ?_
    · intro f hf
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hf ⊢
      rw [map_sub, hf, hf0, sub_self]
    · intro f hf
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hf ⊢
      rw [map_add, hf, hf0, zero_add]
    · intro f _; simp
    · intro f _; simp
  have htot := Finset.card_eq_sum_card_fiberwise (f := L) (s := (univ : Finset (Fin r → k)))
    (t := univ) (fun _ _ => Finset.mem_univ _)
  rw [Finset.sum_congr rfl (fun b _ => hfib b), Finset.sum_const, smul_eq_mul] at htot
  have hcard : Fintype.card (Fin r → k) = Fintype.card k ^ r := by simp
  rw [Finset.card_univ, Finset.card_univ] at htot
  rw [hfib w, ← hcard, htot, Nat.mul_comm]
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
