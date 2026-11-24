-- Prove2me | solution 1 for FairSelling.GeneralTPS.thr_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:41:56.686011+00:00
-- url     : https://prove2.me/submissions/14133396-30c1-4846-b54f-23e523ee950c

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
import Theorems.Thm_FairSelling_TPS_nonneg


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling.GeneralTPS
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (i : Fin n) :
    0 ≤ thr v p i := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (TPS_nonneg (v i) p hp)
end FairSelling.GeneralTPS
