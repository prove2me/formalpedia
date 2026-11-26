-- Prove2me | solution 1 for BandParity.existsUnique_pinned
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:14:30.619827+00:00
-- url     : https://prove2.me/submissions/99e4b2ad-7f05-4545-b7c8-05e6e457b56b

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
public import Theorems.Thm_P2M_BandParity_existsUnique_pinned__ef15a6d526ea


set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution (hp8 : p % 8 = 5) :
    ∃! χ : MulChar (ZMod p) GaussianInt, orderOf χ = 4 ∧ χ 2 = gi :=
  existsUnique_pinned' hp8
end BandParity
