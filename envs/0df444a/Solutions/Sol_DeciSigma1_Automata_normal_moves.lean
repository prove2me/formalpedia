-- Prove2me | solution 1 for DeciSigma1.Automata.normal_moves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:36:58.701935+00:00
-- url     : https://prove2.me/submissions/1d7361f8-8325-484e-adae-c9b38f59bb19

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Theorems.Thm_DeciSigma1_Automata_upperRun_moves
public import Theorems.Thm_DeciSigma1_Automata_lowerRun_moves

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
open DeciSigma1.Constraints
open DeciSigma1.Automata
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
namespace DeciSigma1.Automata
theorem _root_.solution {Γ : List (LitT n V)} {x y : V} {u t : List (Fin n)}
    (h : Normal Γ x u y t) : Moves Γ (x, u) (y, t) := by
  obtain ⟨β, γ, σ, v, rfl, rfl, hp, hq⟩ := h
  exact (upperRun_moves hp σ).trans (lowerRun_moves hq σ)
end DeciSigma1.Automata
