-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.card_fib_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:34.564429+00:00
-- url     : https://prove2.me/submissions/5602958c-79db-4be6-86bb-85104da80225

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_UnramifiedTrace_CardFilterSubtype

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
theorem _root_.solution {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Fintype V] [Fintype W] [DecidableEq W] (f : V →+ W)
    (hf : Function.Surjective f) (w : W) :
    (Finset.univ.filter (fun v => f v = w)).card * Fintype.card W = Fintype.card V := by
  have hall : ∀ w', (Finset.univ.filter (fun v => f v = w')).card =
      (Finset.univ.filter (fun v => f v = w)).card := by
    intro w'
    obtain ⟨a, ha⟩ := hf w'
    obtain ⟨b, hb⟩ := hf w
    refine Finset.card_bij' (fun x _ => x + (b - a)) (fun x _ => x - (b - a)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [map_add, map_sub, hx, ha, hb]
      abel
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [map_sub, map_sub, hx, ha, hb]
      abel
    · intro x _
      abel
    · intro x _
      abel
  calc (Finset.univ.filter (fun v => f v = w)).card * Fintype.card W
      = ∑ w' : W, (Finset.univ.filter (fun v => f v = w')).card := by
        rw [Finset.sum_congr rfl (fun w' _ => hall w'), Finset.sum_const, Finset.card_univ,
          smul_eq_mul, mul_comm]
    _ = Finset.univ.card := (Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)).symm
    _ = Fintype.card V := Finset.card_univ
end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
