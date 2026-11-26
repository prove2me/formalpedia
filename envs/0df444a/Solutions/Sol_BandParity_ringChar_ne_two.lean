-- Prove2me | solution 1 for BandParity.ringChar_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:05:37.302575+00:00
-- url     : https://prove2.me/submissions/c8e2f7a7-72ce-48ff-b33f-58c3794d7c03

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; exact hp2
end BandParity
