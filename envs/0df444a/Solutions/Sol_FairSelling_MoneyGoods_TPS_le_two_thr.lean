-- Prove2me | solution 1 for FairSelling.MoneyGoods.TPS_le_two_thr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:42:23.298273+00:00
-- url     : https://prove2.me/submissions/da5c698e-edf1-4b93-9bcc-8bd3f632574f

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxMoney
import Theorems.Thm_FairSelling_TPS_nonneg


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.MoneyGoods
open GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling.MoneyGoods
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g)
    (j : Fin n) : TPS n (v j) p ≤ 2 * thr v p j := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0:ℝ) < 2 * n - 1 := by linarith
  have ht0 : 0 ≤ TPS n (v j) p := TPS_nonneg (v j) p hp
  have h1 : (1 : ℝ) ≤ 2 * ((n : ℝ) / (2 * n - 1)) := by
    rw [show (2 : ℝ) * ((n : ℝ) / (2 * n - 1)) = (2 * n) / (2 * n - 1) by ring,
      le_div_iff₀ hden]
    linarith
  show TPS n (v j) p ≤ 2 * (((n : ℝ) / (2 * n - 1)) * TPS n (v j) p)
  nlinarith
end FairSelling.MoneyGoods
