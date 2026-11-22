-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.retainedCount_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:50:45.33196+00:00
-- url     : https://prove2.me/submissions/111086c1-bc6d-4104-95e3-328e992ecc04

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_sitePositions
public import Theorems.Thm_DeciSigma1_Words_retainedCount_add_of_not_mem


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {δ : ℕ} {cs : Finset ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {p q : ℕ} (hp : Retained δ cs p) (hpq : p ≤ q)
    (hno : ∀ c ∈ cs, ¬ (p ≤ c ∧ c < q)) :
    retainedCount (sitePositions δ cs) q = retainedCount (sitePositions δ cs) p + (q - p) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hpq
  rw [retainedCount_add_of_not_mem, Nat.add_sub_cancel_left]
  intro i hi hm
  obtain ⟨c, hc, h1, h2⟩ := mem_sitePositions.mp hm
  by_cases h : p ≤ c
  · exact hno c hc ⟨h, by omega⟩
  · exact hp c hc ⟨by omega, by omega⟩
end DeciSigma1.Holes.Fresh
