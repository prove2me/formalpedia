-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.qcounting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:52:43.815136+00:00
-- url     : https://prove2.me/submissions/c55884de-956a-460d-9373-d3fdc60b9327

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_P2M_FairSelling_PotTPS_QStage_pot_nonneg__175ac3e55641
import Theorems.Thm_FairSelling_PotTPS_QStage_sum_biUnion_le
import Theorems.Thm_FairSelling_PotTPS_QStage_cost_eq_zero_of_notMem
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_ChargeTPS_cost_eq_zero_of_notMem
import Theorems.Thm_FairSelling_ChargeTPS_saleLoss_nonneg
import Theorems.Thm_FairSelling_ChargeTPS_sum_saleLoss
import Theorems.Thm_FairSelling_GeneralTPS_thr_nonneg
import Theorems.Thm_FairSelling_GeneralTPS_truncBundle_univ
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_truncBundle_sdiff
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
theorem _root_.solution (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {s : QStage G n} (hs : s.Good v p eps)
    (j : Fin n) (hj : j ∉ s.served) :
    (2 * ((n : ℝ) - s.served.card) - 1) * GeneralTPS.thr v p j
      ≤ truncBundle (v j) p (TPS n (v j) p) s.pool
        + (s.bank - ∑ g ∈ s.cutSet, min (s.pot p g) (GeneralTPS.thr v p j)) := by
  classical
  set w := v j with hw
  set t := TPS n (v j) p with ht
  set τ := GeneralTPS.thr v p j with hτ
  have hτ0 : 0 ≤ τ := GeneralTPS.thr_nonneg v p hn hp j
  set B : Finset G := Finset.univ.biUnion s.bundle with hB
  set OW : Finset G := Finset.univ.biUnion s.own with hOW
  -- the truncated value of everything
  have hUniv : truncBundle w p t Finset.univ = (2 * (n:ℝ) - 1) * τ := by
    rw [GeneralTPS.truncBundle_univ w p hn hp, hτ, hw]
    unfold GeneralTPS.thr
    have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hne : ((n:ℝ) * 2 - 1) ≠ 0 := ne_of_gt (by linarith)
    field_simp
  -- the universe splits
  have hdisjSB : Disjoint s.sold B := by
    refine Finset.disjoint_left.mpr (fun x hx hxB => ?_)
    simp only [hB, Finset.mem_biUnion, Finset.mem_univ, true_and] at hxB
    obtain ⟨k, hk⟩ := hxB
    exact Finset.disjoint_left.mp (hs.sold_bundle k) hx hk
  have hsplit : truncBundle w p t Finset.univ
      = truncBundle w p t s.pool + truncBundle w p t (s.sold ∪ B) := by
    rw [truncBundle_sdiff w p t (Finset.subset_univ (s.sold ∪ B))]
    rfl
  have hSB : truncBundle w p t (s.sold ∪ B)
      = truncBundle w p t s.sold + truncBundle w p t B :=
    Finset.sum_union hdisjSB
  have hbund : truncBundle w p t B = ∑ i, truncBundle w p t (s.bundle i) := by
    unfold truncBundle
    rw [hB]
    exact Finset.sum_biUnion (fun a _ b _ hab => hs.bundle_disj a b hab)
  -- the sold goods split into the self-financed sales and the cut goods
  have hdisjOWcut : Disjoint OW s.cutSet := by
    refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
    simp only [hOW, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
    simp only [cutSet, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx'
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hx'
    exact Finset.disjoint_left.mp (hs.own_cut a b) ha hb
  have hlosssold : ∑ g ∈ s.sold, saleLoss w p t g
      = (∑ i, ∑ g ∈ s.own i, saleLoss w p t g) + ∑ g ∈ s.cutSet, saleLoss w p t g := by
    show ∑ g ∈ OW ∪ s.cutSet, saleLoss w p t g = _
    rw [Finset.sum_union hdisjOWcut]
    congr 1
    rw [hOW]
    exact Finset.sum_biUnion (fun a _ b _ hab => hs.own_disj a b hab)
  have hsoldtrunc : truncBundle w p t s.sold
      = (∑ g ∈ s.sold, p g) + ∑ g ∈ s.sold, saleLoss w p t g := by
    rw [sum_saleLoss w p t s.sold]; ring
  -- the total cost
  have hcost : ∑ i, s.cost v p i j
      = (∑ i, truncBundle w p t (s.bundle i)) + (∑ i, s.cash i) + (∑ i, s.resv i)
        + (∑ i, ∑ g ∈ s.own i, saleLoss w p t g)
        + ∑ i, ∑ g ∈ s.src i, (saleLoss w p t g + min (s.pot p g) τ) := by
    unfold cost
    rw [← hw, ← ht, ← hτ]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
  -- the cut goods are charged at least once each
  have hcut : ∑ g ∈ s.cutSet, (saleLoss w p t g + min (s.pot p g) τ)
      ≤ ∑ i, ∑ g ∈ s.src i, (saleLoss w p t g + min (s.pot p g) τ) := by
    refine sum_biUnion_le Finset.univ s.src _ (fun g => ?_)
    have h1 : 0 ≤ saleLoss w p t g := saleLoss_nonneg w p t g
    have h2 : 0 ≤ min (s.pot p g) τ := le_min (pot_nonneg' hp hs g) hτ0
    linarith
  have hcutsplit : ∑ g ∈ s.cutSet, (saleLoss w p t g + min (s.pot p g) τ)
      = (∑ g ∈ s.cutSet, saleLoss w p t g) + ∑ g ∈ s.cutSet, min (s.pot p g) τ :=
    Finset.sum_add_distrib
  have hmoney := hs.money
  have hkey : ∑ i, s.cost v p i j
      ≥ (2 * (n:ℝ) - 1) * τ - truncBundle w p t s.pool
        - (s.bank - ∑ g ∈ s.cutSet, min (s.pot p g) τ) := by
    rw [hcost]
    have h1 : truncBundle w p t s.pool + truncBundle w p t s.sold
        + (∑ i, truncBundle w p t (s.bundle i)) = (2 * (n:ℝ) - 1) * τ := by
      rw [← hUniv, hsplit, hSB, hbund]; ring
    rw [hsoldtrunc, hlosssold] at h1
    linarith [hcut, hcutsplit]
  -- the cost bound, summed
  have hbound : ∑ i, s.cost v p i j ≤ (s.served.card : ℝ) * (2 * τ) := by
    have hsub : ∑ i, s.cost v p i j = ∑ i ∈ s.served, s.cost v p i j := by
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro i _ hi
      exact cost_eq_zero_of_notMem hs hi j
    rw [hsub]
    calc ∑ i ∈ s.served, s.cost v p i j
        ≤ ∑ _i ∈ s.served, (2 * τ) :=
          Finset.sum_le_sum (fun i hi => hs.cost_le i hi j hj)
      _ = (s.served.card : ℝ) * (2 * τ) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hexp : (2 * ((n : ℝ) - s.served.card) - 1) * τ
      = (2 * (n:ℝ) - 1) * τ - (s.served.card : ℝ) * (2 * τ) := by ring
  rw [hexp]
  linarith
end FairSelling.PotTPS.QStage
