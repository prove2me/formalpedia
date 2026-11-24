-- Prove2me | solution 1 for FairSelling.vbarSum_eq_sum_of_price_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:28:09.268355+00:00
-- url     : https://prove2.me/submissions/3779694c-ceeb-48c6-85b7-4e65aefefda0

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution {vi p : G → ℝ} {A : Finset G} (hv : ∀ g, 0 ≤ vi g)
    (hp : ∀ g ∈ A, p g = 0) : vbarSum vi p A = ∑ g ∈ A, vi g := by
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [vbar, hp g hg]
  exact max_eq_right (hv g)
end FairSelling
