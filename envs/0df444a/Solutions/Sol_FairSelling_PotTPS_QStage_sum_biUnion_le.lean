-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.sum_biUnion_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:44.542695+00:00
-- url     : https://prove2.me/submissions/3697eaef-18a9-48a0-9451-12b0e070f15c

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
omit [Fintype G]
namespace FairSelling.PotTPS.QStage
theorem _root_.solution {ι : Type*} (T : Finset ι) (u : ι → Finset G) (f : G → ℝ)
    (hf : ∀ g, 0 ≤ f g) : ∑ g ∈ T.biUnion u, f g ≤ ∑ i ∈ T, ∑ g ∈ u i, f g := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | insert a T ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      have h1 := Finset.sum_union_inter (s₁ := u a) (s₂ := T.biUnion u) (f := f)
      have h2 : 0 ≤ ∑ g ∈ (u a) ∩ (T.biUnion u), f g := Finset.sum_nonneg (fun g _ => hf g)
      linarith
end FairSelling.PotTPS.QStage
