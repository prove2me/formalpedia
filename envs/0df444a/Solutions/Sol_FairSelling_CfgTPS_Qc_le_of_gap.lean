-- Prove2me | solution 1 for FairSelling.CfgTPS.Qc_le_of_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:41:14.647501+00:00
-- url     : https://prove2.me/submissions/b3e7d093-e529-4905-b852-3a855749e378

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
import Definitions.Def_RequestProject_TPSSefxConfig
import Theorems.Thm_FairSelling_CfgTPS_gapMin_le

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.CfgTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (w : Fin n → G → ℝ) (p : G → ℝ) (req : Fin n → ℝ) (k0 : Fin n)
omit [Fintype G] [DecidableEq G]
namespace FairSelling.CfgTPS
theorem _root_.solution {S : Finset G} {c : ℝ} (hc : 0 ≤ c) (m : Fin n)
    (h : req m - vbarSum (w m) p S ≤ c) : Qc w p req k0 S ≤ c :=
  max_le hc (le_trans (gapMin_le w p req k0 S m) h)
end FairSelling.CfgTPS
