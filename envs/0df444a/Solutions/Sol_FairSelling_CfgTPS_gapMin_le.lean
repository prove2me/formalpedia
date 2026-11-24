-- Prove2me | solution 1 for FairSelling.CfgTPS.gapMin_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:31:05.557205+00:00
-- url     : https://prove2.me/submissions/7c5607ae-8e11-4326-a634-887626e76044

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
theorem _root_.solution (S : Finset G) (m : Fin n) :
    gapMin w p req k0 S ≤ req m - vbarSum (w m) p S :=
  Finset.inf'_le _ (Finset.mem_univ m)
end FairSelling.CfgTPS
