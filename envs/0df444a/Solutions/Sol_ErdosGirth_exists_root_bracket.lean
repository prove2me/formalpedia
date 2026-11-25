-- Prove2me | solution 1 for ErdosGirth.exists_root_bracket
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:31:22.797101+00:00
-- url     : https://prove2.me/submissions/50ec1fbc-f767-49a6-a672-8342006003f4

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
namespace ErdosGirth
theorem _root_.solution (E M : ℕ) (hE : E ≠ 0) : ∃ q : ℕ, q ^ E ≤ M ∧ M < (q + 1) ^ E := by
  have hex : ∃ k : ℕ, M < (k + 1) ^ E := ⟨M, lt_of_lt_of_le (Nat.lt_succ_self M)
    (Nat.le_self_pow hE _)⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases h : Nat.find hex with _ | j
  · simp [zero_pow hE]
  · have := Nat.find_min hex (m := j) (by omega)
    exact le_of_not_gt this
end ErdosGirth
