-- Prove2me | solution 1 for FairSelling.Canonical.sold_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:08:54.266806+00:00
-- url     : https://prove2.me/submissions/80465563-d14c-4566-8289-c949ccab0b46

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsMatching
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Theorems.Thm_FairSelling_Canonical_sold_subset_sell

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.Canonical
variable {w p : G → ℝ} {μ t : ℝ} {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ}
omit [Fintype G]
namespace FairSelling.Canonical
theorem _root_.solution (C : Canonical w p μ t k R D) (J : Finset (Fin k)) : C.sold J ⊆ R :=
  (C.sold_subset_sell J).trans C.sell_subset
end FairSelling.Canonical
