-- Prove2me | solution 1 for FairSelling.thr_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:09:47.651312+00:00
-- url     : https://prove2.me/submissions/d203f7e1-9018-4b5d-95e4-ffdcc736fcfb

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
import Theorems.Thm_FairSelling_MMS_nonneg


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hv : ∀ i g, 0 ≤ v i g)
    (hp : ∀ g, 0 ≤ p g) (i : Fin n) : 0 ≤ thr v p i :=
  mul_nonneg (by norm_num [rho]) (MMS_nonneg hn (v i) p (hv i) hp)
end FairSelling
