-- Prove2me | solution 1 for ConjCoord.Proof.gCount_eq_cntL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:50:43.964155+00:00
-- url     : https://prove2.me/submissions/87d2b96e-66ea-4812-86d1-c84ffc59344a

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Compute
public import Theorems.Thm_ConjCoord_Proof_count_eq_cntL

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (m : ℕ) : gCount m = cntL 1 1 16 m qG := by
  rw [← count_eq_cntL 1 1 16 m one_pos one_pos (by norm_num)
    (fun x y => (x ^ 2 + y ^ 2) % 16 = 5 ∧ (y % 16 = 6 ∨ y % 16 = 10)) qG ?_]
  · unfold gCount
    congr 1
    exact filter_congr fun v _ => by push_cast; simp only [one_mul]
  · intro x y
    have hx : ((x.natAbs ^ 2 : ℕ) : ℤ) = x ^ 2 := by push_cast; exact sq_abs x
    have hy : ((y.natAbs ^ 2 : ℕ) : ℤ) = y ^ 2 := by push_cast; exact sq_abs y
    simp only [qG, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
    rw [← hx, ← hy]
    rcases Int.natAbs_eq y with hy' | hy' <;>
    · constructor <;> intro h <;> omega
end ConjCoord.Proof
