-- Prove2me | solution 1 for Erdos338Proof.ncard_Iio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:10.771422+00:00
-- url     : https://prove2.me/submissions/f68ada87-4afa-4a28-85f0-d81f96a304e6

module
public import Definitions.Def_Erdos338_Pairs
public import Definitions.Def_Erdos338_Residue
public import Definitions.Def_Erdos338_Shift
public import Definitions.Def_Erdos338_Main

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos338Proof
namespace Erdos338Proof
theorem _root_.solution (b : ℕ) : (Set.Iio b).ncard = b := by
  have e : Set.Iio b = ↑(range b) := by
    ext x
    simp
  rw [e, Set.ncard_coe_finset, card_range]
end Erdos338Proof
