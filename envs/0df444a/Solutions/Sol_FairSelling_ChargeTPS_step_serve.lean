-- Prove2me | solution 1 for FairSelling.ChargeTPS.step_serve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:05.760639+00:00
-- url     : https://prove2.me/submissions/bfbf10f0-9736-4806-84a5-07adb751a22e

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
import Theorems.Thm_FairSelling_ChargeTPS_CStage_disjoint_pool_soldSet
import Theorems.Thm_FairSelling_ChargeTPS_CStage_disjoint_pool_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_disjoint_pool_charge
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
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open CStage
namespace FairSelling.ChargeTPS
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (heps : 0 ≤ eps)
    {s : CStage G n} (hs : s.Good v p eps)
    {k : Fin n} (hk : k ∉ s.served)
    {S S₀ : Finset G} (hSpool : S ⊆ s.pool) (hS₀pool : S₀ ⊆ s.pool) (hSS₀ : Disjoint S S₀)
    {q r : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hbank : 0 ≤ s.bank + (∑ g ∈ S₀, p g) - q - r)
    (hclaim : GeneralTPS.thr v p k ≤ vbarSum (v k) p S + q)
    (hkeep : ∀ g ∈ S, p g ≤ v k g)
    (hsafenew : ∀ j, j ≠ k →
      (vbarSum (v j) p S + q ≤ s.req v p eps j) ∨
      (q = 0 ∧ ∀ g ∈ S, vbarSum (v j) p (S \ {g}) + p g ≤ s.req v p eps j))
    (hcostnew : ∀ j, j ∉ s.served → j ≠ k →
      truncBundle (v j) p (TPS n (v j) p) S + q + r
        + ∑ g ∈ S₀, saleLoss (v j) p (TPS n (v j) p) g ≤ 2 * GeneralTPS.thr v p j) :
    ∃ s' : CStage G n, s'.Good v p eps ∧ s.served.card < s'.served.card := by
  classical
  obtain ⟨hempty, hbdisj, hcdisj, hcb, hcash0, hresv0, hbank0, hmoney, hshare, hsafe, hcost⟩ := hs
  obtain ⟨hkb, hkc, hkcash, hkresv⟩ := hempty k hk
  refine ⟨⟨insert k s.served, Function.update s.bundle k S, Function.update s.charge k S₀,
      Function.update s.cash k q, Function.update s.resv k r,
      s.bank + (∑ g ∈ S₀, p g) - q - r⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals
    dsimp only
  · -- unserved agents hold nothing
    intro i hi
    have hik : i ≠ k := fun h => hi (by rw [h]; exact Finset.mem_insert_self _ _)
    have his : i ∉ s.served := fun h => hi (Finset.mem_insert_of_mem h)
    obtain ⟨h1, h2, h3, h4⟩ := hempty i his
    rw [Function.update_of_ne hik, Function.update_of_ne hik, Function.update_of_ne hik,
      Function.update_of_ne hik]
    exact ⟨h1, h2, h3, h4⟩
  · -- bundles are pairwise disjoint
    intro i j hij
    by_cases hi : i = k
    · rw [hi, Function.update_self, Function.update_of_ne (fun h => hij (hi.trans h.symm))]
      exact Finset.disjoint_of_subset_left hSpool (disjoint_pool_bundle s j)
    · by_cases hj : j = k
      · rw [hj, Function.update_self, Function.update_of_ne hi]
        exact (Finset.disjoint_of_subset_left hSpool (disjoint_pool_bundle s i)).symm
      · rw [Function.update_of_ne hi, Function.update_of_ne hj]; exact hbdisj i j hij
  · -- charges are pairwise disjoint
    intro i j hij
    by_cases hi : i = k
    · rw [hi, Function.update_self, Function.update_of_ne (fun h => hij (hi.trans h.symm))]
      exact Finset.disjoint_of_subset_left hS₀pool (disjoint_pool_charge s j)
    · by_cases hj : j = k
      · rw [hj, Function.update_self, Function.update_of_ne hi]
        exact (Finset.disjoint_of_subset_left hS₀pool (disjoint_pool_charge s i)).symm
      · rw [Function.update_of_ne hi, Function.update_of_ne hj]; exact hcdisj i j hij
  · -- charges are disjoint from bundles
    intro i j
    by_cases hi : i = k
    · rw [hi, Function.update_self]
      by_cases hj : j = k
      · rw [hj, Function.update_self]; exact hSS₀.symm
      · rw [Function.update_of_ne hj]
        exact Finset.disjoint_of_subset_left hS₀pool (disjoint_pool_bundle s j)
    · rw [Function.update_of_ne hi]
      by_cases hj : j = k
      · rw [hj, Function.update_self]
        exact (Finset.disjoint_of_subset_left hSpool (disjoint_pool_charge s i)).symm
      · rw [Function.update_of_ne hj]; exact hcb i j
  · intro i
    by_cases hi : i = k
    · rw [hi, Function.update_self]; exact hq
    · rw [Function.update_of_ne hi]; exact hcash0 i
  · intro i
    by_cases hi : i = k
    · rw [hi, Function.update_self]; exact hr
    · rw [Function.update_of_ne hi]; exact hresv0 i
  · exact hbank
  · -- the money equation
    have hsold' : CStage.soldSet
        ⟨insert k s.served, Function.update s.bundle k S, Function.update s.charge k S₀,
          Function.update s.cash k q, Function.update s.resv k r,
          s.bank + (∑ g ∈ S₀, p g) - q - r⟩ = s.soldSet ∪ S₀ := by
      ext x
      simp only [CStage.soldSet, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_union]
      constructor
      · rintro ⟨i, hi⟩
        by_cases h : i = k
        · rw [h, Function.update_self] at hi; exact Or.inr hi
        · rw [Function.update_of_ne h] at hi; exact Or.inl ⟨i, hi⟩
      · rintro (⟨i, hi⟩ | hi)
        · refine ⟨i, ?_⟩
          by_cases h : i = k
          · rw [h, hkc] at hi; exact absurd hi (Finset.notMem_empty x)
          · rw [Function.update_of_ne h]; exact hi
        · exact ⟨k, by rw [Function.update_self]; exact hi⟩
    have hdisjSS₀ : Disjoint s.soldSet S₀ :=
      Finset.disjoint_left.mpr (fun x hx hx' =>
        Finset.disjoint_left.mp (disjoint_pool_soldSet s) (hS₀pool hx') hx)
    have h1 : ∑ i, Function.update s.cash k q i = (∑ i, s.cash i) + q := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
      have : ∑ i ∈ Finset.univ \ {k}, s.cash i = (∑ i, s.cash i) - s.cash k := by
        rw [eq_sub_iff_add_eq, Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]; simp
      rw [this, hkcash]; ring
    have h2 : ∑ i, Function.update s.resv k r i = (∑ i, s.resv i) + r := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
      have : ∑ i ∈ Finset.univ \ {k}, s.resv i = (∑ i, s.resv i) - s.resv k := by
        rw [eq_sub_iff_add_eq, Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]; simp
      rw [this, hkresv]; ring
    rw [h1, h2, hsold', Finset.sum_union hdisjSS₀]
    linarith
  · -- share
    intro i hi
    by_cases hik : i = k
    · rw [hik, Function.update_self, Function.update_self]; exact hclaim
    · rw [Function.update_of_ne hik, Function.update_of_ne hik]
      exact hshare i ((Finset.mem_insert.mp hi).resolve_left hik)
  · -- safety
    intro i hi j
    have hreqmono : s.req v p eps j ≤ CStage.req v p eps
        ⟨insert k s.served, Function.update s.bundle k S, Function.update s.charge k S₀,
          Function.update s.cash k q, Function.update s.resv k r,
          s.bank + (∑ g ∈ S₀, p g) - q - r⟩ j := by
      by_cases hj : j = k
      · rw [hj]
        simp only [CStage.req, if_neg hk, if_pos (Finset.mem_insert_self k s.served),
          Function.update_self]
        linarith [hclaim]
      · by_cases hjs : j ∈ s.served
        · have hmem : j ∈ insert k s.served := Finset.mem_insert_of_mem hjs
          simp only [CStage.req, if_pos hjs, if_pos hmem, Function.update_of_ne hj]
          exact le_rfl
        · have hmem : j ∉ insert k s.served := fun h =>
            hjs ((Finset.mem_insert.mp h).resolve_left hj)
          simp only [CStage.req, if_neg hjs, if_neg hmem]
          exact le_rfl
    simp only [CStage.CSafe]
    by_cases hik : i = k
    · rw [hik, Function.update_self, Function.update_self]
      by_cases hjk : j = k
      · left
        have hreq' : CStage.req v p eps
            ⟨insert k s.served, Function.update s.bundle k S, Function.update s.charge k S₀,
              Function.update s.cash k q, Function.update s.resv k r,
              s.bank + (∑ g ∈ S₀, p g) - q - r⟩ j = vbarSum (v j) p S + q + eps := by
          rw [hjk]
          simp only [CStage.req, if_pos (Finset.mem_insert_self k s.served),
            Function.update_self]
        rw [hreq']
        linarith
      · rcases hsafenew j hjk with h | ⟨hq0, h⟩
        · exact Or.inl (le_trans h hreqmono)
        · exact Or.inr ⟨hq0, hkeep, fun g hg => le_trans (h g hg) hreqmono⟩
    · have his : i ∈ s.served := (Finset.mem_insert.mp hi).resolve_left hik
      rw [Function.update_of_ne hik, Function.update_of_ne hik]
      rcases hsafe i his j with h | ⟨h1, h2, h3⟩
      · exact Or.inl (le_trans h hreqmono)
      · exact Or.inr ⟨h1, h2, fun g hg => le_trans (h3 g hg) hreqmono⟩
  · -- cost
    intro i hi j hj
    have hjk : j ≠ k := fun h => hj (by rw [h]; exact Finset.mem_insert_self _ _)
    have hjs : j ∉ s.served := fun h => hj (Finset.mem_insert_of_mem h)
    simp only [CStage.cost]
    by_cases hik : i = k
    · rw [hik, Function.update_self, Function.update_self, Function.update_self,
        Function.update_self]
      exact hcostnew j hjs hjk
    · have his : i ∈ s.served := (Finset.mem_insert.mp hi).resolve_left hik
      rw [Function.update_of_ne hik, Function.update_of_ne hik, Function.update_of_ne hik,
        Function.update_of_ne hik]
      exact hcost i his j hjs
  · -- one more agent is served
    rw [Finset.card_insert_of_notMem hk]
    omega
end FairSelling.ChargeTPS
