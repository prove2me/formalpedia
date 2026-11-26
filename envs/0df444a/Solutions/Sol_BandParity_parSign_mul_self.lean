-- Prove2me | solution 1 for BandParity.parSign_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:21.191907+00:00
-- url     : https://prove2.me/submissions/87f8389d-1cb3-4eb1-9c6b-b56b3e2997b9

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
public import Theorems.Thm_BandParity_parSign_eq

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp
namespace BandParity
theorem _root_.solution (x : ZMod p) : parSign x * parSign x = 1 := by
  rcases parSign_eq x with h | h <;> rw [h] <;> norm_num
end BandParity
