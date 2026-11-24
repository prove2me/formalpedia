-- Prove2me | solution 1 for FairSelling.PhaseTPS.pureGood_of_TPS_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:10.294217+00:00
-- url     : https://prove2.me/submissions/49d631b7-aa03-4702-a3de-a048c9a91353

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling.PhaseTPS
theorem _root_.solution {v : Fin n → G → ℝ} {p : G → ℝ} {A : Finset (Fin n)} {g : G}
    (h : ∀ j, j ∉ A → TPS n (v j) p ≤ p g) : PureGood v p A g := by
  intro j hj
  unfold saleLoss trunc
  have h1 : min (v j g) (TPS n (v j) p) ≤ p g := le_trans (min_le_right _ _) (h j hj)
  rw [max_eq_left h1]
  ring
end FairSelling.PhaseTPS
