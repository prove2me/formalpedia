-- Prove2me | solution 1 for DeciSigma1.Arithmetic.DifferenceSystem.isWalk_append_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:10.328803+00:00
-- url     : https://prove2.me/submissions/ffdc519a-27ac-450c-96ed-9a8ec78ff8d7

module
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
open DeciSigma1.Arithmetic.DifferenceSystem
variable {ι : Type} (D : DifferenceSystem ι)
variable {D}
namespace DeciSigma1.Arithmetic.DifferenceSystem
theorem _root_.solution {p : List ι} {i j : ι} (hp : D.IsWalk p)
    (hl : p.getLast? = some i) (hij : (D.edgeWeight i j).isSome) : D.IsWalk (p ++ [j]) := by
  unfold IsWalk at hp ⊢
  rw [List.isChain_append]
  refine ⟨hp, List.isChain_singleton _, ?_⟩
  intro x hx y hy
  rw [hl, Option.mem_some_iff] at hx
  simp only [List.head?_cons, Option.mem_some_iff] at hy
  subst hx; subst hy; exact hij
end DeciSigma1.Arithmetic.DifferenceSystem
