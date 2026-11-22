-- Prove2me | solution 1 for DeciSigma1.Automata.derivedPairs_moves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:35:15.931101+00:00
-- url     : https://prove2.me/submissions/50326fd4-6e8f-4c4a-a7ae-6d77907b2218

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Theorems.Thm_DeciSigma1_Constraints_mem_derivedPairs


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
open DeciSigma1.Constraints
open DeciSigma1.Automata
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
namespace DeciSigma1.Automata
theorem _root_.solution {Γ : List (LitT n V)} {a b : V} (h : (a, b) ∈ derivedPairs Γ)
    (w : List (Fin n)) : Moves Γ (a, w) (b, w) := by
  have hh := (mem_derivedPairs Γ a b).mp h
  clear h
  induction hh generalizing w with
  | refl => exact .refl
  | lit h => exact .single (.copy h)
  | trans _ _ ih₁ ih₂ => exact (ih₁ w).trans (ih₂ w)
  | decomp c hl _ hu ih => exact ((ih (c :: w)).head (.push c hl)).tail (.pop c hu)
end DeciSigma1.Automata
