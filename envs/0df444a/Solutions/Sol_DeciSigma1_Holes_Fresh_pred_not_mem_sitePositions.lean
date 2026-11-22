-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.pred_not_mem_sitePositions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:27:46.63699+00:00
-- url     : https://prove2.me/submissions/c66dd68d-57c1-4db0-afc7-f7cc2662f11a

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_sitePositions


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {δ : ℕ} {cs : Finset ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {p : ℕ} (hp : Retained δ cs p) (hpr : ∀ c ∈ cs, p ≠ c + δ) :
    p = 0 ∨ p - 1 ∉ sitePositions δ cs := by
  by_cases h0 : p = 0
  · exact Or.inl h0
  · refine Or.inr fun h => ?_
    obtain ⟨c, hc, h1, h2⟩ := mem_sitePositions.mp h
    have := hpr c hc
    exact hp c hc ⟨by omega, by omega⟩
end DeciSigma1.Holes.Fresh
