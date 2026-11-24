-- Prove2me | solution 1 for FairSelling.Canonical.sold_subset_sell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:12:09.559449+00:00
-- url     : https://prove2.me/submissions/afadf492-44c2-4c35-88dc-50bd33660d34

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsMatching
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Theorems.Thm_FairSelling_Canonical_mem_sold

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.Canonical
variable {w p : G → ℝ} {μ t : ℝ} {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ}
omit [Fintype G]
namespace FairSelling.Canonical
theorem _root_.solution (C : Canonical w p μ t k R D) (J : Finset (Fin k)) :
    C.sold J ⊆ C.sell := by
  intro f hf
  obtain ⟨j, _, hj⟩ := mem_sold.mp hf
  exact C.src_mem j f hj
end FairSelling.Canonical
