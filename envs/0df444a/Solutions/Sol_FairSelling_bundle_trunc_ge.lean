-- Prove2me | solution 1 for FairSelling.bundle_trunc_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:32.480125+00:00
-- url     : https://prove2.me/submissions/293741b6-0c2f-4444-84a2-b4b16344c7e2

import Mathlib
import Definitions.Def_RequestProject_Selling

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v : G → ℝ) (hv : ∀ g, 0 ≤ v g) (o : Outcome G n)
    (j : Fin n) (r : ℝ) (hr : 0 ≤ r) (hmj : 0 ≤ o.money j) (hj : r ≤ util v o j) :
    r ≤ (∑ g ∈ o.kept j, min (v g) r) + o.money j := by
  by_cases h_exists : ∃ g ∈ o.kept j, r ≤ v g;
  · obtain ⟨ g, hg₁, hg₂ ⟩ := h_exists;
    exact le_add_of_le_of_nonneg ( le_trans ( by aesop ) ( Finset.single_le_sum ( fun x _ => le_min ( hv x ) hr ) hg₁ ) ) hmj;
  · unfold util at hj; simp_all +decide [ min_eq_left_of_lt ] ;
end FairSelling
