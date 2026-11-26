-- Prove2me | solution 1 for Erdos338Proof.card_rep_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:44.442721+00:00
-- url     : https://prove2.me/submissions/67946b5d-c0d8-4aac-80b2-7d5fe0ddc2ae

module
public import Definitions.Def_Erdos338_Structure
public import Definitions.Def_Erdos338_Pairs

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Erdos338Proof
namespace Erdos338Proof
theorem _root_.solution (A : Set ℕ) (m : ℕ) : #(rep A m) ≤ m + 1 := by
  classical
  unfold rep
  exact (card_filter_le _ _).trans (card_range _).le
end Erdos338Proof
