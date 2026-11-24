-- Prove2me | solution 1 for FairSelling.ChargeTPS.vbarSum_nonneg_of_price
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:28.981084+00:00
-- url     : https://prove2.me/submissions/ec7cc253-20d5-49b7-a9db-8773a50a34ca

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
omit [Fintype G] [DecidableEq G]
namespace FairSelling.ChargeTPS
theorem _root_.solution (hp : ∀ g, 0 ≤ p g) (u : G → ℝ) (A : Finset G) :
    0 ≤ vbarSum u p A :=
  Finset.sum_nonneg (fun g _ => le_trans (hp g) (le_max_left _ _))
end FairSelling.ChargeTPS
