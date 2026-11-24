-- Prove2me | solution 1 for FairSelling.CfgTPS.Qc_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:23:51.690735+00:00
-- url     : https://prove2.me/submissions/6f2cd21e-cb3a-4be4-a2da-8a63c1712832

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
import Definitions.Def_RequestProject_TPSSefxConfig

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.CfgTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (w : Fin n → G → ℝ) (p : G → ℝ) (req : Fin n → ℝ) (k0 : Fin n)
omit [Fintype G] [DecidableEq G]
namespace FairSelling.CfgTPS
theorem _root_.solution (S : Finset G) : 0 ≤ Qc w p req k0 S := le_max_left _ _
end FairSelling.CfgTPS
