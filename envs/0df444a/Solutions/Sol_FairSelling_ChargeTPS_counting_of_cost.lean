-- Prove2me | solution 1 for FairSelling.ChargeTPS.counting_of_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:32:22.717798+00:00
-- url     : https://prove2.me/submissions/ee3b57ec-e1a8-4e99-ba24-4279c1e0b898

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxCharge
import Theorems.Thm_FairSelling_ChargeTPS_sum_saleLoss
import Theorems.Thm_FairSelling_ChargeTPS_cost_eq_zero_of_notMem
import Theorems.Thm_FairSelling_GeneralTPS_truncBundle_univ
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_truncBundle_sdiff
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open CStage
namespace FairSelling.ChargeTPS
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) {s : CStage G n} (hs : s.Good v p eps) (j : Fin n) (hj : j ∉ s.served) :
    (2 * ((n : ℝ) - s.served.card) - 1) * GeneralTPS.thr v p j
      ≤ truncBundle (v j) p (TPS n (v j) p) s.pool + s.bank := by
  classical
  set w := v j with hw
  set t := TPS n (v j) p with ht
  set B : Finset G := Finset.univ.biUnion s.bundle with hB
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  -- the truncated value of everything
  have hUniv : truncBundle w p t Finset.univ = (2 * (n:ℝ) - 1) * GeneralTPS.thr v p j := by
    rw [GeneralTPS.truncBundle_univ w p hn hp]
    unfold GeneralTPS.thr
    have hne : ((n:ℝ) * 2 - 1) ≠ 0 := ne_of_gt (by linarith)
    rw [hw]
    field_simp
  -- the universe splits into pool, sold goods and bundles
  have hdisjSB : Disjoint s.soldSet B := by
    refine Finset.disjoint_left.mpr (fun x hx hxB => ?_)
    simp only [CStage.soldSet, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
    simp only [hB, Finset.mem_biUnion, Finset.mem_univ, true_and] at hxB
    obtain ⟨i, hi⟩ := hx
    obtain ⟨k, hk⟩ := hxB
    exact Finset.disjoint_left.mp (hs.2.2.2.1 i k) hi hk
  have hsplit : truncBundle w p t Finset.univ
      = truncBundle w p t s.pool + truncBundle w p t (s.soldSet ∪ B) := by
    rw [truncBundle_sdiff w p t (Finset.subset_univ (s.soldSet ∪ B))]
    rfl
  have hSB : truncBundle w p t (s.soldSet ∪ B)
      = truncBundle w p t s.soldSet + truncBundle w p t B :=
    Finset.sum_union hdisjSB
  have hsold : truncBundle w p t s.soldSet = ∑ i, truncBundle w p t (s.charge i) := by
    unfold CStage.soldSet truncBundle
    refine Finset.sum_biUnion ?_
    intro a _ b _ hab
    exact hs.2.2.1 a b hab
  have hbund : truncBundle w p t B = ∑ i, truncBundle w p t (s.bundle i) := by
    unfold truncBundle
    rw [hB]
    refine Finset.sum_biUnion ?_
    intro a _ b _ hab
    exact hs.2.1 a b hab
  have hpsold : ∑ g ∈ s.soldSet, p g = ∑ i, ∑ g ∈ s.charge i, p g := by
    unfold CStage.soldSet
    refine Finset.sum_biUnion ?_
    intro a _ b _ hab
    exact hs.2.2.1 a b hab
  -- the total cost
  have hcost : ∑ i, s.cost v p i j
      = (∑ i, truncBundle w p t (s.bundle i)) + (∑ i, s.cash i) + (∑ i, s.resv i)
        + ((∑ i, truncBundle w p t (s.charge i)) - ∑ i, ∑ g ∈ s.charge i, p g) := by
    unfold CStage.cost
    rw [← hw, ← ht]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => sum_saleLoss w p t (s.charge i))
  have hmoney := hs.2.2.2.2.2.2.2.1
  have hkey : ∑ i, s.cost v p i j
      = (2 * (n:ℝ) - 1) * GeneralTPS.thr v p j - truncBundle w p t s.pool - s.bank := by
    rw [hcost]
    rw [hpsold] at hmoney
    have h1 : truncBundle w p t s.pool + (∑ i, truncBundle w p t (s.charge i))
        + (∑ i, truncBundle w p t (s.bundle i)) = (2 * (n:ℝ) - 1) * GeneralTPS.thr v p j := by
      rw [← hUniv, hsplit, hSB, hsold, hbund]; ring
    linarith
  -- the cost bound, summed
  have hbound : ∑ i, s.cost v p i j ≤ (s.served.card : ℝ) * (2 * GeneralTPS.thr v p j) := by
    have hsub : ∑ i, s.cost v p i j = ∑ i ∈ s.served, s.cost v p i j := by
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro i _ hi
      exact cost_eq_zero_of_notMem v p eps hs hi j
    rw [hsub]
    calc ∑ i ∈ s.served, s.cost v p i j
        ≤ ∑ _i ∈ s.served, (2 * GeneralTPS.thr v p j) :=
          Finset.sum_le_sum (fun i hi => hs.2.2.2.2.2.2.2.2.2.2 i hi j hj)
      _ = (s.served.card : ℝ) * (2 * GeneralTPS.thr v p j) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  linarith [hkey, hbound]
end FairSelling.ChargeTPS
