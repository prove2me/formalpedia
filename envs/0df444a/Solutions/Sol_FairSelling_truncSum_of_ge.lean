-- Prove2me | solution 1 for FairSelling.truncSum_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:52:07.242481+00:00
-- url     : https://prove2.me/submissions/1a29e552-1768-4f00-b91b-69d5bb393768

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) {t : ℝ} (ht : ∀ g, v g ≤ t) :
    truncSum n v p t = PS n v p := by
  unfold truncSum PS
  congr 1
  exact Finset.sum_congr rfl (fun g _ => by rw [min_eq_left (ht g)])
end FairSelling
