-- Prove2me | solution 1 for FairSelling.MoneyGoods.price_eq_zero_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:43:14.35923+00:00
-- url     : https://prove2.me/submissions/d95850a5-e7e8-48af-98f1-4d287380e825

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxMoney
import Theorems.Thm_FairSelling_MoneyGoods_mem_soldGoods

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.MoneyGoods
open GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling.MoneyGoods
theorem _root_.solution {p : G → ℝ} {g : G} (h : g ∉ soldGoods p) : p g = 0 := by
  by_contra hc
  exact h (mem_soldGoods.2 hc)
end FairSelling.MoneyGoods
