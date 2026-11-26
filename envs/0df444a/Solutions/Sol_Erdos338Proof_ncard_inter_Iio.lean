-- Prove2me | solution 1 for Erdos338Proof.ncard_inter_Iio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:44.899701+00:00
-- url     : https://prove2.me/submissions/faf2df34-5971-4c5e-a5ee-71f5d24cca8e

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
theorem _root_.solution (S : Set ℕ) (b : ℕ) : (S ∩ Set.Iio b).ncard = cnt S b := by
  classical
  have e : S ∩ Set.Iio b = ↑((range b).filter (· ∈ S)) := by
    ext x
    simp [and_comm]
  rw [e, Set.ncard_coe_finset]
  unfold cnt
  convert rfl
end Erdos338Proof
