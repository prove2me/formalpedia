-- Prove2me | solution 1 for ConjCoord.Proof.mem_sol111
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:51:10.834957+00:00
-- url     : https://prove2.me/submissions/0ea52754-fef1-4cc1-bb6d-da5c957a5d62

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps
public import Theorems.Thm_ConjCoord_Proof_mem_sol

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
variable {n : ℕ}
namespace ConjCoord.Proof
theorem _root_.solution {m : ℕ} (v : ℤ × ℤ × ℤ) :
    v ∈ sol 1 1 1 m ↔ v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = m := by
  rw [mem_sol one_pos one_pos one_pos]; push_cast; simp only [one_mul]
end ConjCoord.Proof
