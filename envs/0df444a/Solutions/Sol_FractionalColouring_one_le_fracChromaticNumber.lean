-- Prove2me | solution 1 for FractionalColouring.one_le_fracChromaticNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:41:08.333838+00:00
-- url     : https://prove2.me/submissions/a644ff72-ca5c-4323-b7c3-a489adc2fb06

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
public import Definitions.Def_FractionalLib_Basic
public import Theorems.Thm_FractionalColouring_IsFracClique_sum_le_fracChromaticNumber
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
theorem _root_.solution [Nonempty V] : 1 ≤ fracChromaticNumber G := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have hg : IsFracClique G (fun u => if u = v then 1 else 0) := by
    refine ⟨fun u => by dsimp only; split_ifs <;> norm_num, fun s _ => ?_⟩
    rw [Finset.sum_ite_eq']
    split_ifs <;> norm_num
  simpa using hg.sum_le_fracChromaticNumber
end FractionalColouring
