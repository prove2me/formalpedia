-- Prove2me | solution 1 for FairSelling.exists_minimal_subset_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:11:22.902928+00:00
-- url     : https://prove2.me/submissions/a66c9fbc-f6ae-4ff4-90a7-b3da42ea20ed

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsBagFilling

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [DecidableEq G]
namespace FairSelling
theorem _root_.solution (f : G → ℝ) (τ : ℝ) :
    ∀ A : Finset G, τ ≤ ∑ g ∈ A, f g →
      ∃ B ⊆ A, τ ≤ ∑ g ∈ B, f g ∧ ∀ e ∈ B, ∑ g ∈ B.erase e, f g < τ := by
  intro A
  induction A using Finset.strongInduction with
  | _ A ih =>
    intro hA
    by_cases hex : ∃ e ∈ A, τ ≤ ∑ g ∈ A.erase e, f g
    · obtain ⟨e, he, hle⟩ := hex
      obtain ⟨B, hBsub, h1, h2⟩ := ih (A.erase e) (Finset.erase_ssubset he) hle
      exact ⟨B, hBsub.trans (Finset.erase_subset _ _), h1, h2⟩
    · push_neg at hex
      exact ⟨A, Finset.Subset.refl _, hA, hex⟩
end FairSelling
