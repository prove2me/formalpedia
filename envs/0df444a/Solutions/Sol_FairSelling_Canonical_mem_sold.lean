-- Prove2me | solution 1 for FairSelling.Canonical.mem_sold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:10:05.30743+00:00
-- url     : https://prove2.me/submissions/7ddc5401-591f-44e3-ad23-20ded296ae3c

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsMatching
import Definitions.Def_RequestProject_TwoThirdsCanonical

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.Canonical
variable {w p : G → ℝ} {μ t : ℝ} {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ}
omit [Fintype G]
namespace FairSelling.Canonical
theorem _root_.solution {C : Canonical w p μ t k R D} {J : Finset (Fin k)} {f : G} :
    f ∈ C.sold J ↔ ∃ j ∈ J, C.src j = some f := by
  simp [sold, Option.mem_toFinset]
end FairSelling.Canonical
