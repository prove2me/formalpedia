-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.greatestPreimage_site
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:51:23.987351+00:00
-- url     : https://prove2.me/submissions/2a666fb5-0b7e-4626-900b-763687f74b91

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Theorems.Thm_DeciSigma1_Holes_Fresh_StrictlySeparated_lt
public import Theorems.Thm_DeciSigma1_Holes_Fresh_retainedCount_site_right
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_sitePositions
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_retainedCount


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {δ : ℕ} {cs : Finset ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (hs : StrictlySeparated δ cs) {c : ℕ} (hc : c ∈ cs) :
    greatestPreimage (sitePositions δ cs) (retainedCount (sitePositions δ cs) c) = c + δ := by
  rw [← retainedCount_site_right hc]
  refine greatestPreimage_retainedCount fun h => ?_
  obtain ⟨c', hc', h1, h2⟩ := mem_sitePositions.mp h
  rcases lt_trichotomy c c' with h | h | h
  · have := hs.lt hc hc' h; omega
  · omega
  · have := hs.lt hc' hc h; omega
end DeciSigma1.Holes.Fresh
