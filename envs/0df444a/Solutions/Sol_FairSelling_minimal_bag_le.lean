-- Prove2me | solution 1 for FairSelling.minimal_bag_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:11:25.984527+00:00
-- url     : https://prove2.me/submissions/b7ea5117-40ce-4279-a077-a999c2ba1e42

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsBagFilling

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [DecidableEq G]
namespace FairSelling
theorem _root_.solution {f : G → ℝ} {τ ε : ℝ} (hτ : 0 ≤ τ) (hε : 0 ≤ ε) {B : Finset G}
    (hsmall : ∀ g ∈ B, f g ≤ ε) (hge : τ ≤ ∑ g ∈ B, f g)
    (hmin : ∀ e ∈ B, ∑ g ∈ B.erase e, f g < τ) :
    ∑ g ∈ B, f g ≤ τ + ε := by
  rcases Finset.eq_empty_or_nonempty B with rfl | ⟨e, he⟩
  · simp only [Finset.sum_empty] at hge ⊢
    linarith
  · have hsplit : ∑ g ∈ B, f g = f e + ∑ g ∈ B.erase e, f g := (Finset.add_sum_erase B f he).symm
    have h1 := hmin e he
    have h2 := hsmall e he
    linarith
end FairSelling
