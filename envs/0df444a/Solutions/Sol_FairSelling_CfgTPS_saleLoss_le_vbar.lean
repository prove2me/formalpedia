-- Prove2me | solution 1 for FairSelling.CfgTPS.saleLoss_le_vbar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:27.319176+00:00
-- url     : https://prove2.me/submissions/48ac9b51-4559-4fed-9692-0eccab5d58e8

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
import Definitions.Def_RequestProject_TPSSefxConfig
import Theorems.Thm_FairSelling_trunc_le_vbar


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.CfgTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable {w : Fin n → G → ℝ} {p : G → ℝ} {req : Fin n → ℝ} {k0 : Fin n} {D : ℝ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling.CfgTPS
theorem _root_.solution (t : ℝ) (u : G → ℝ) (g : G) :
    ChargeTPS.saleLoss u p t g ≤ vbar u p g - p g := by
  have := trunc_le_vbar u p t g
  unfold ChargeTPS.saleLoss
  linarith
end FairSelling.CfgTPS
