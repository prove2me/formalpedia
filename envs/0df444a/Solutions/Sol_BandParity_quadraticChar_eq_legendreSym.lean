-- Prove2me | solution 1 for BandParity.quadraticChar_eq_legendreSym
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:05:41.941243+00:00
-- url     : https://prove2.me/submissions/0d567645-d8d2-4a4b-a8ab-3809f07b3af2

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution (x : ZMod p) :
    quadraticChar (ZMod p) x = legendreSym p (x.val : ℤ) := by
  unfold legendreSym; simp
end BandParity
