-- Prove2me | solution 1 for BandParity.zero_ne_neg_gi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:14:04.31467+00:00
-- url     : https://prove2.me/submissions/e1b242bd-2806-42d1-a856-4f85d08658d3

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
theorem _root_.solution : (0 : GaussianInt) ≠ -gi := by decide
end BandParity
