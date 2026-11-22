-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.retained_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:47:25.352825+00:00
-- url     : https://prove2.me/submissions/89d11e16-0e23-4765-86a9-49b160f9b5ce

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
theorem _root_.solution {n : ℕ} (h : ∀ c ∈ cs, c + δ ≤ n) : Retained δ cs n := by
  rintro c hc ⟨-, h2⟩; have := h c hc; omega
end DeciSigma1.Holes.Fresh
