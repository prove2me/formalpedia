-- Prove2me | solution 1 for BandParity.gi_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:01:16.622208+00:00
-- url     : https://prove2.me/submissions/e42c21db-a47e-4a60-abd6-d947678e15b7

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution : gi ≠ 0 := by decide
end BandParity
