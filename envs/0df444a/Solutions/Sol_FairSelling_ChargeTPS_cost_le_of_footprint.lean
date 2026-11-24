-- Prove2me | solution 1 for FairSelling.ChargeTPS.cost_le_of_footprint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:44:03.441802+00:00
-- url     : https://prove2.me/submissions/1f2e0dc4-69b3-4cd3-abb1-f4f04d4f2cb5

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
import Theorems.Thm_FairSelling_ChargeTPS_sum_saleLoss


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]
namespace FairSelling.ChargeTPS
theorem _root_.solution (w p : G → ℝ) (t : ℝ) (S S₀ : Finset G) (hdisj : Disjoint S S₀)
    (q r : ℝ) (hqr : q + r = ∑ g ∈ S₀, p g) :
    truncBundle w p t S + q + r + ∑ g ∈ S₀, saleLoss w p t g = truncBundle w p t (S ∪ S₀) := by
  rw [sum_saleLoss, truncBundle, truncBundle, truncBundle, Finset.sum_union hdisj]
  linarith
end FairSelling.ChargeTPS
