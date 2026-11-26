-- Prove2me | solution 1 for BandParity.val_neg_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:54:07.621291+00:00
-- url     : https://prove2.me/submissions/c1696467-7f0b-40c9-b4fd-84888f6d1edf

module
public import Definitions.Def_BandParity_Basic
public import Definitions.Def_BandParity_FixedBase
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]
namespace BandParity
theorem _root_.solution {n : ZMod p} (hn : n ≠ 0) : (-n).val = p - n.val := by
  have := ZMod.val_lt n
  have h := ZMod.neg_val n
  simpa [hn] using h
end BandParity
