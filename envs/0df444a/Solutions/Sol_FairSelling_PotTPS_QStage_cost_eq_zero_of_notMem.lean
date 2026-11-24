-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.cost_eq_zero_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:48.416315+00:00
-- url     : https://prove2.me/submissions/44b94ed9-1b05-4fba-b7ce-a5c292284c45

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
variable {v p eps}
namespace FairSelling.PotTPS.QStage
theorem _root_.solution {s : QStage G n} (hs : s.Good v p eps) {i : Fin n}
    (hi : i ∉ s.served) (j : Fin n) : s.cost v p i j = 0 := by
  obtain ⟨hb, ho, hc, hcash, hresv⟩ := hs.unserved i hi
  simp [cost, hb, ho, hc, hcash, hresv, truncBundle]
end FairSelling.PotTPS.QStage
