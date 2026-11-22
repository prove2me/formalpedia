-- Prove2me | solution 1 for DeciSigma1.Full.Closure.popRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:11:46.778303+00:00
-- url     : https://prove2.me/submissions/7b764289-6ae4-49a4-8dea-b41e615b3ffd

module
public import Mathlib.Data.Fintype.Powerset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Theorems.Thm_DeciSigma1_Full_Closure_signed_upper_neg
public import Theorems.Thm_DeciSigma1_Automata_mem_upperStep
public import Theorems.Thm_DeciSigma1_Automata_upperRun_snoc
attribute [local simp] DeciSigma1.Automata.mem_upperStep
attribute [local simp] DeciSigma1.Automata.upperRun_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
variable [Fintype V] [DecidableEq V]
namespace DeciSigma1.Full.Closure
theorem _root_.solution {x : V × Bool} {β : List (Fin n)} {i : Fin n}
    (h : (Automata.upperRun (signed c Γ) x (β ++ [i])).Nonempty) :
    ∃ r ∈ Automata.upperRun (signed c Γ) x β, Neg Γ (r.1, r.2, []) := by
  obtain ⟨a, ha⟩ := h
  rw [Automata.upperRun_snoc, Automata.mem_upperStep] at ha
  obtain ⟨r, hr, a, hl, _⟩ := ha
  exact ⟨r, hr, signed_upper_neg hl⟩
end DeciSigma1.Full.Closure
