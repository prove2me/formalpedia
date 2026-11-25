-- Prove2me | solution 1 for ConjCoord.Proof.mem_Icc_of_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:47:17.734279+00:00
-- url     : https://prove2.me/submissions/a154fb02-b2c6-44d4-9a65-e580619529d8

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution {x : ℤ} {n : ℕ} (h : x ^ 2 ≤ n) : x ∈ Icc (-(n : ℤ)) n := by
  have h1 := Int.le_self_sq x
  have h2 := Int.le_self_sq (-x)
  rw [neg_sq] at h2
  simp only [mem_Icc]; constructor <;> linarith
end ConjCoord.Proof
