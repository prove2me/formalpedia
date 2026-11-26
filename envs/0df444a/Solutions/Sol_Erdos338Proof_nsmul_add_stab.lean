-- Prove2me | solution 1 for Erdos338Proof.nsmul_add_stab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:41.361639+00:00
-- url     : https://prove2.me/submissions/1161e097-8e72-4dbf-86a0-181a326a06db

module
public import Mathlib
public import Definitions.Def_Erdos338_Kneser_Kneser
public import Definitions.Def_Erdos338_Covering

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
open Erdos338Proof
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
namespace Erdos338Proof
theorem _root_.solution (s H : Finset G) (hH : H + H = H) {h : ℕ} (hh : 1 ≤ h) :
    h • (s + H) = h • s + H := by
  induction h, hh using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [succ_nsmul, ih, succ_nsmul]
    calc n • s + H + (s + H) = n • s + s + (H + H) := by abel
      _ = n • s + s + H := by rw [hH]
end Erdos338Proof
