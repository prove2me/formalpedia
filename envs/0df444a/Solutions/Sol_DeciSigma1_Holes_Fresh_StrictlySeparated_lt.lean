-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.StrictlySeparated.lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:47:04.979981+00:00
-- url     : https://prove2.me/submissions/82d0f1f2-cc57-4727-9e69-36765edf56c0

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {δ : ℕ} {cs : Finset ℕ}
namespace DeciSigma1.Holes.Fresh
namespace StrictlySeparated
theorem _root_.solution (h : StrictlySeparated δ cs) {c c' : ℕ} (hc : c ∈ cs)
    (hc' : c' ∈ cs) (hlt : c < c') : c + δ < c' := h c hc c' hc' hlt
end StrictlySeparated
end DeciSigma1.Holes.Fresh
