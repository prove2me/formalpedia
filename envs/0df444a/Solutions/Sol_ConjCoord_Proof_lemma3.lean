-- Prove2me | solution 1 for ConjCoord.Proof.lemma3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:55:07.493806+00:00
-- url     : https://prove2.me/submissions/4bf112df-b92c-466b-b205-7dd3b2ac9ef6

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps
public import Theorems.Thm_ConjCoord_Proof_r3_eq_three_mul_reps122
public import Theorems.Thm_ConjCoord_Proof_r3_two_mul_eq
public import Theorems.Thm_ConjCoord_Proof_reps112_eq

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
variable {n : ℕ}
namespace ConjCoord.Proof
theorem _root_.solution {p : ℕ} (hp : p % 16 = 5) :
    r3 p = 3 * reps 1 2 2 p ∧ r3 (2 * p) = 6 * reps 1 2 4 p := by
  refine ⟨r3_eq_three_mul_reps122 (by omega), ?_⟩
  rw [r3_two_mul_eq (by omega), reps112_eq (by omega)]; ring
end ConjCoord.Proof
