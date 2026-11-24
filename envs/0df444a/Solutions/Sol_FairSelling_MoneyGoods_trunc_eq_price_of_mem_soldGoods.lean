-- Prove2me | solution 1 for FairSelling.MoneyGoods.trunc_eq_price_of_mem_soldGoods
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:42:04.467808+00:00
-- url     : https://prove2.me/submissions/a5a93ec4-5b12-4508-92e6-3b98c11dee29

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
theorem _root_.solution {v : Fin n → G → ℝ} {p : G → ℝ}
    (hclass : MoneyClass v p) {g : G} (hg : g ∈ soldGoods p) (j : Fin n) :
    trunc (v j) p (TPS n (v j) p) g = p g := by
  rcases hclass g with h | h
  · exact absurd h (mem_soldGoods.1 hg)
  · exact h j
end FairSelling.MoneyGoods
