-- Prove2me | solution 1 for BandParity.zero_ne_gi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:02:56.546724+00:00
-- url     : https://prove2.me/submissions/465c2c24-fd62-4d72-8761-be503735a756

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
theorem _root_.solution : (0 : GaussianInt) ≠ gi := by decide
end BandParity
