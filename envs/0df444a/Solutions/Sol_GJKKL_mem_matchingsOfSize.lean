-- Prove2me | solution 1 for GJKKL.mem_matchingsOfSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:52.841934+00:00
-- url     : https://prove2.me/submissions/6bdec3e7-fc6b-4b87-b250-9ff12d9ca566

module
public import Definitions.Def_RequestProject_Pseudorandom_Defs
public import Definitions.Def_GJKKL_Statement

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [DecidableEq V]
namespace GJKKL
theorem _root_.solution {H M : Finset (Finset V)} {m : ℕ} :
    M ∈ matchingsOfSize H m ↔ M ⊆ H ∧ IsMatching M ∧ M.card = m := by
  classical
  simp [matchingsOfSize]
end GJKKL
