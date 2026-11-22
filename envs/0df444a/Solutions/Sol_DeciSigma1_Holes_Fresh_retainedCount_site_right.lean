-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.retainedCount_site_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:50:45.843079+00:00
-- url     : https://prove2.me/submissions/a5f73e63-6ea6-47c7-8f2f-c0ea7ac1dc56

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
theorem _root_.solution {c : ℕ} (hc : c ∈ cs) :
    retainedCount (sitePositions δ cs) (c + δ) = retainedCount (sitePositions δ cs) c :=
  retainedCount_add_of_mem fun i hi => mem_sitePositions.mpr ⟨c, hc, by omega, by omega⟩
end DeciSigma1.Holes.Fresh
