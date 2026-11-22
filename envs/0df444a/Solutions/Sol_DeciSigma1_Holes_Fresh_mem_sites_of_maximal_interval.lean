-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.mem_sites_of_maximal_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:26:35.751607+00:00
-- url     : https://prove2.me/submissions/3f2e8a3b-77af-47f8-a1be-4f1a3c51a14e

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_sitePositions

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
variable {W : Fin k → List α}
variable {δ : ℕ} {cs : Finset ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (hs : StrictlySeparated δ cs) {j c : ℕ} (hjc : j < c)
    (hD : ∀ p, j ≤ p → p < c → p ∈ sitePositions δ cs)
    (hj : j = 0 ∨ j - 1 ∉ sitePositions δ cs) (hc : c ∉ sitePositions δ cs) :
    j ∈ cs ∧ c = j + δ := by
  obtain ⟨c₀, hc₀, h1, h2⟩ := mem_sitePositions.mp (hD (c - 1) (by omega) (by omega))
  have hce : c = c₀ + δ := by
    by_contra hne
    exact hc (mem_sitePositions.mpr ⟨c₀, hc₀, by omega, by omega⟩)
  have hje : j = c₀ := by
    rcases lt_trichotomy j c₀ with h | h | h
    · obtain ⟨c₁, hc₁, h3, h4⟩ := mem_sitePositions.mp (hD (c₀ - 1) (by omega) (by omega))
      have := hs c₁ hc₁ c₀ hc₀ (by omega)
      omega
    · exact h
    · rcases hj with h0 | h0
      · omega
      · exact absurd (mem_sitePositions.mpr ⟨c₀, hc₀, by omega, by omega⟩) h0
  exact ⟨hje ▸ hc₀, by omega⟩
end DeciSigma1.Holes.Fresh
