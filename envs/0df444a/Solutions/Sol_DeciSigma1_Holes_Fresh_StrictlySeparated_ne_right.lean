-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.StrictlySeparated.ne_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:04:00.994809+00:00
-- url     : https://prove2.me/submissions/d129c1cc-1458-42de-bc3e-c0c5085731fe

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Theorems.Thm_DeciSigma1_Holes_Fresh_StrictlySeparated_lt

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {δ : ℕ} {cs : Finset ℕ}
namespace DeciSigma1.Holes.Fresh
namespace StrictlySeparated
theorem _root_.solution (h : StrictlySeparated δ cs) (hδ : 0 < δ) {c c' : ℕ}
    (hc : c ∈ cs) (hc' : c' ∈ cs) : c ≠ c' + δ := by
  intro he
  have := h.lt hc' hc (by omega)
  omega
end StrictlySeparated
end DeciSigma1.Holes.Fresh
