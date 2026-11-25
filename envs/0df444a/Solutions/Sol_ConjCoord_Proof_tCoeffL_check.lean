-- Prove2me | solution 1 for ConjCoord.Proof.tCoeffL_check
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:47:14.932617+00:00
-- url     : https://prove2.me/submissions/e27fac26-7f34-4337-8063-3d52f8ddcf0f

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Compute

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution : ∀ m < 513, (64 : ℤ) ∣ tCoeffL m := by decide +kernel
end ConjCoord.Proof
