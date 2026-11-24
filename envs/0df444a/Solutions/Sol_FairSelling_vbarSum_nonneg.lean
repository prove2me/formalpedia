-- Prove2me | solution 1 for FairSelling.vbarSum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:50:29.429922+00:00
-- url     : https://prove2.me/submissions/19e553c0-3cf6-4f94-978a-f25375221f31

import Mathlib
import Definitions.Def_RequestProject_Selling

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
omit [Fintype G]
namespace FairSelling
theorem _root_.solution {vi p : G → ℝ} (hv : ∀ g, 0 ≤ vi g) (A : Finset G) :
    0 ≤ vbarSum vi p A :=
  Finset.sum_nonneg fun g _ => le_trans (hv g) (le_max_right _ _)
end FairSelling
