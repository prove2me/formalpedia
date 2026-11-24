-- Prove2me | solution 1 for FairSelling.exists_canonical_of_few_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:48:36.726362+00:00
-- url     : https://prove2.me/submissions/bd2d80ad-ed1e-4352-a5d6-e32bb3fcd25a

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsBagFilling
import Definitions.Def_RequestProject_TwoThirdsProp6
import Theorems.Thm_FairSelling_exists_canonical_of_large_pairs

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {μ : ℝ} (hμ : 0 ≤ μ)
    {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ} (hD : 0 ≤ D) {A C S : Finset G}
    (hRdef : R = A ∪ C ∪ S)
    (hAC : Disjoint A C) (hAS : Disjoint A S) (hCS : Disjoint C S)
    (hA1 : ∀ g ∈ A, μ / 3 ≤ vbar w p g) (hsmall : ∀ g ∈ R, vbar w p g ≤ 2 * μ / 3)
    (hC1 : ∀ g ∈ C, vbar w p g ≤ μ / 3)
    (hS1 : ∀ g ∈ S, μ / 3 ≤ p g) (hS2 : ∀ g ∈ S, w g ≤ p g)
    (hcard : A.card ≤ k)
    (hbud : ((k : ℝ) - 1) * μ + 2 * μ / 3
      ≤ (∑ g ∈ A, vbar w p g) + (∑ g ∈ C, vbar w p g) + D + ∑ g ∈ S, p g) :
    Nonempty (Canonical w p μ (2 * μ / 3) k R D) :=
  exists_canonical_of_large_pairs w p hp hμ hD hRdef hAC hAS hCS hA1 hsmall hC1 hS1 hS2
    (t := 0) (by omega) (by simpa using hbud)
end FairSelling
