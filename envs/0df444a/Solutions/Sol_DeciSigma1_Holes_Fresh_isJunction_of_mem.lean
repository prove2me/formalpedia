-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.isJunction_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:59:05.392278+00:00
-- url     : https://prove2.me/submissions/d04c0285-2500-4280-88ae-60d3d148ae5e

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_sitePositions
public import Theorems.Thm_DeciSigma1_Words_retainedCount_add_of_mem


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {δ : ℕ} {cs : Finset ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {p : ℕ} (hp : p ∈ sitePositions δ cs) :
    IsJunction δ cs (retainedCount (sitePositions δ cs) p) := by
  obtain ⟨c, hc, h1, h2⟩ := mem_sitePositions.mp hp
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h1
  exact ⟨c, hc, (retainedCount_add_of_mem fun i hi =>
    mem_sitePositions.mpr ⟨c, hc, by omega, by omega⟩).symm⟩
end DeciSigma1.Holes.Fresh
