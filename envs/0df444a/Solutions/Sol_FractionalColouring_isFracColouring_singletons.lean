-- Prove2me | solution 1 for FractionalColouring.isFracColouring_singletons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:29:57.007299+00:00
-- url     : https://prove2.me/submissions/1f041126-94e7-4f57-9494-80bf1c7b8c7b

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
public import Definitions.Def_FractionalLib_Basic
public import Theorems.Thm_FiniteLP_toE_apply
attribute [local simp] FiniteLP.toE_apply



set_option autoImplicit true
@[expose] public section
public section
open Finset
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {G}
namespace FractionalColouring
theorem _root_.solution : IsFracColouring G singletonColouring := by
  refine ⟨fun s => by unfold singletonColouring; split_ifs <;> norm_num, fun s hs => ?_,
    fun v => ?_⟩
  · unfold singletonColouring
    rw [if_neg]
    intro h
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact hs (by simp)
  · refine le_trans ?_ (Finset.single_le_sum (f := singletonColouring)
      (fun s _ => by unfold singletonColouring; split_ifs <;> norm_num)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ {v}, Finset.mem_singleton_self v⟩))
    simp [singletonColouring]
end FractionalColouring
