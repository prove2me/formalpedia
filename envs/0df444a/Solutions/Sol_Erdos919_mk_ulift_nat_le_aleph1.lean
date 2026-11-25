-- Prove2me | solution 1 for Erdos919.mk_ulift_nat_le_aleph1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:18:39.28056+00:00
-- url     : https://prove2.me/submissions/3ab4f27a-df97-45c3-a65c-cff18ad1bfc1

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution : #(ULift.{u} ℕ) ≤ ℵ₁ := by
  rw [mk_uLift, mk_nat, lift_aleph0]; exact aleph0_le_aleph 1
end Erdos919
