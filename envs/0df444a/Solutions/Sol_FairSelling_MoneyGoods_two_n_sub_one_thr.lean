-- Prove2me | solution 1 for FairSelling.MoneyGoods.two_n_sub_one_thr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:42:26.360807+00:00
-- url     : https://prove2.me/submissions/a2ff7486-480b-41a3-bd39-1e680df28932

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxMoney

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.MoneyGoods
open GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling.MoneyGoods
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (j : Fin n) :
    (2 * (n : ℝ) - 1) * thr v p j = (n : ℝ) * TPS n (v j) p := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hden : (2 * (n:ℝ) - 1) ≠ 0 := by intro h; linarith
  show (2 * (n : ℝ) - 1) * (((n : ℝ) / (2 * n - 1)) * TPS n (v j) p) = _
  field_simp
end FairSelling.MoneyGoods
