-- Prove2me | solution 1 for BrooksTheorem.Aux.exists_perm2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:36:20.993953+00:00
-- url     : https://prove2.me/submissions/9293ddbe-4810-46d7-9cb2-8b236bb6b4c8

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore
public import Theorems.Thm_BrooksTheorem_Aux_restr_adj
public import Theorems.Thm_BrooksTheorem_Aux_mem_nb
attribute [local simp] BrooksTheorem.Aux.mem_nb


attribute [local simp] BrooksTheorem.Aux.restr_adj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
namespace BrooksTheorem.Aux
theorem _root_.solution {k : ℕ} {a b a' b' : Fin k} (hab : a ≠ b) (hab' : a' ≠ b') :
    ∃ σ : Equiv.Perm (Fin k), σ a = a' ∧ σ b = b' := by
  refine ⟨(Equiv.swap a a').trans (Equiv.swap (Equiv.swap a a' b) b'), ?_, ?_⟩
  · have h1 : Equiv.swap a a' b ≠ a' := by
      intro h
      apply hab
      apply (Equiv.swap a a').injective
      rw [h, Equiv.swap_apply_left]
    simp only [Equiv.trans_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne h1.symm hab'
  · simp
end BrooksTheorem.Aux
