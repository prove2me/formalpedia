-- Prove2me | solution 1 for FairSelling.PhaseTPS.pstep_assign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:25.640714+00:00
-- url     : https://prove2.me/submissions/3164d25c-b9d3-4101-9a91-99336df3d4cb

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhase
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPhaseStep
import Theorems.Thm_FairSelling_PhaseTPS_sum_update_eq
import Theorems.Thm_FairSelling_ChargeTPS_CStage_disjoint_pool_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_disjoint_pool_charge
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_ChargeTPS_TPS_le_two_thr
import Theorems.Thm_FairSelling_ChargeTPS_cash_add_saleLoss_le
import Theorems.Thm_FairSelling_ChargeTPS_thr_le_TPS
import Theorems.Thm_FairSelling_GeneralTPS_thr_nonneg
import Theorems.Thm_FairSelling_PhaseTPS_PStage_disjoint_pool_bundle
import Theorems.Thm_FairSelling_PhaseTPS_PStage_disjoint_pool_charge
import Theorems.Thm_FairSelling_PhaseTPS_PStage_disjoint_pool_sold
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bank
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bundle
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_cash
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_resv
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_served
import Theorems.Thm_FairSelling_PhaseTPS_PureGood_mono
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_bank
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_bundle
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_cash
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_resv
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_served
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.PhaseTPS
theorem _root_.solution (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : PStage G n} (hs : s.Good v p eps) {k : Fin n}
    {S S₀own S₀ext : Finset G}
    (hSpool : S ⊆ s.pool) (hOpool : S₀own ⊆ s.pool) (hEpool : S₀ext ⊆ s.pool)
    (hSO : Disjoint S S₀own) (hSE : Disjoint S S₀ext) (hOE : Disjoint S₀own S₀ext)
    {q r : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hfin : q + r ≤ s.bank + (s.cash k + s.resv k - ∑ g ∈ s.own k, p g)
              + (∑ g ∈ S₀own, p g) + ∑ g ∈ S₀ext, p g)
    (hself : ∑ g ∈ S₀own, p g ≤ q + r)
    (hpure : (∀ g ∈ S₀ext, PureGood v p (insert k s.served) g) ∨
      (S = ∅ ∧ S₀own = ∅ ∧ r = 0 ∧ ∃ g0, S₀ext = {g0} ∧ q ≤ p g0))
    (hclaim : s.req v p eps k ≤ vbarSum (v k) p S + q)
    (hkeep : ∀ g ∈ S, p g ≤ v k g)
    (hsafenew : ∀ j, j ≠ k → (vbarSum (v j) p S + q ≤ s.req v p eps j) ∨
      (q = 0 ∧ ∀ g ∈ S, vbarSum (v j) p (S \ {g}) + p g ≤ s.req v p eps j))
    (hcostnew : ∀ j, j ∉ insert k s.served →
      truncBundle (v j) p (TPS n (v j) p) S + q + r
        + ∑ g ∈ S₀own, saleLoss (v j) p (TPS n (v j) p) g ≤ 2 * GeneralTPS.thr v p j)
    (hkpure : ∀ g ∈ s.ext k, PureGood v p s.served g) :
    ∃ s' : PStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by
  classical
  set A := ∑ g ∈ S₀own, p g with hA
  set B := ∑ g ∈ S₀ext, p g with hB
  set C := ∑ g ∈ s.own k, p g with hC
  set s' : PStage G n :=
    ⟨insert k s.served, Function.update s.bundle k S, Function.update s.own k S₀own,
      Function.update s.ext k (s.ext k ∪ S₀ext), Function.update s.cash k q,
      Function.update s.resv k r, s.bank + (s.cash k + s.resv k - C) + A + B - q - r⟩ with hs'
  -- ### the fields of the new state
  have hbundle_k : s'.bundle k = S := by simp [hs']
  have hbundle_ne : ∀ i, i ≠ k → s'.bundle i = s.bundle i := by
    intro i hi; simp [hs', Function.update_of_ne hi]
  have hown_k : s'.own k = S₀own := by simp [hs']
  have hown_ne : ∀ i, i ≠ k → s'.own i = s.own i := by
    intro i hi; simp [hs', Function.update_of_ne hi]
  have hext_k : s'.ext k = s.ext k ∪ S₀ext := by simp [hs']
  have hext_ne : ∀ i, i ≠ k → s'.ext i = s.ext i := by
    intro i hi; simp [hs', Function.update_of_ne hi]
  have hcash_k : s'.cash k = q := by simp [hs']
  have hcash_ne : ∀ i, i ≠ k → s'.cash i = s.cash i := by
    intro i hi; simp [hs', Function.update_of_ne hi]
  have hresv_k : s'.resv k = r := by simp [hs']
  have hresv_ne : ∀ i, i ≠ k → s'.resv i = s.resv i := by
    intro i hi; simp [hs', Function.update_of_ne hi]
  have hserved' : s'.served = insert k s.served := rfl
  have hcharge_ne : ∀ i, i ≠ k → s'.charge i = s.charge i := by
    intro i hi; simp [PStage.charge, hown_ne i hi, hext_ne i hi]
  have hcharge_k : s'.charge k = S₀own ∪ (s.ext k ∪ S₀ext) := by
    simp [PStage.charge, hown_k, hext_k]
  -- ### disjointness of the new goods from the old state
  have hpool_charge : ∀ {X : Finset G}, X ⊆ s.pool → ∀ i, Disjoint X (s.charge i) := by
    intro X hX i
    exact Finset.disjoint_of_subset_left hX (PStage.disjoint_pool_charge s i)
  have hpool_bundle : ∀ {X : Finset G}, X ⊆ s.pool → ∀ i, Disjoint X (s.bundle i) := by
    intro X hX i
    exact Finset.disjoint_of_subset_left hX (PStage.disjoint_pool_bundle s i)
  have hpool_own : ∀ {X : Finset G}, X ⊆ s.pool → ∀ i, Disjoint X (s.own i) := by
    intro X hX i
    exact Finset.disjoint_of_subset_right Finset.subset_union_left (hpool_charge hX i)
  have hpool_ext : ∀ {X : Finset G}, X ⊆ s.pool → ∀ i, Disjoint X (s.ext i) := by
    intro X hX i
    exact Finset.disjoint_of_subset_right Finset.subset_union_right (hpool_charge hX i)
  have hownk_disj : ∀ i, i ≠ k → Disjoint (s.own k) (s.charge i) := by
    intro i hi
    exact Finset.disjoint_union_right.mpr ⟨hs.own_disj k i (Ne.symm hi), hs.own_ext k i⟩
  have hownk_extk : Disjoint (s.own k) (s.ext k) := hs.own_ext k k
  have hownk_sold : s.own k ⊆ s.sold := fun x hx =>
    Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, Finset.mem_union_left _ hx⟩
  -- ### the new sold set and the money
  have hsold : s'.sold = (s.sold \ s.own k) ∪ (S₀own ∪ S₀ext) := by
    ext x
    simp only [PStage.sold, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_sdiff]
    constructor
    · rintro ⟨i, hi⟩
      by_cases hik : i = k
      · subst hik
        rw [hcharge_k] at hi
        rcases Finset.mem_union.mp hi with h | h
        · exact Or.inr (Or.inl h)
        · rcases Finset.mem_union.mp h with h | h
          · exact Or.inl ⟨⟨i, Finset.mem_union_right _ h⟩,
              fun hx => Finset.disjoint_left.mp hownk_extk hx h⟩
          · exact Or.inr (Or.inr h)
      · rw [hcharge_ne i hik] at hi
        exact Or.inl ⟨⟨i, hi⟩, fun hx => Finset.disjoint_left.mp (hownk_disj i hik) hx hi⟩
    · rintro (⟨⟨i, hi⟩, hx⟩ | h | h)
      · by_cases hik : i = k
        · subst hik
          rcases Finset.mem_union.mp hi with h | h
          · exact absurd h hx
          · refine ⟨i, ?_⟩
            rw [hcharge_k]
            exact Finset.mem_union_right _ (Finset.mem_union_left _ h)
        · refine ⟨i, ?_⟩
          rw [hcharge_ne i hik]
          exact hi
      · refine ⟨k, ?_⟩
        rw [hcharge_k]
        exact Finset.mem_union_left _ h
      · refine ⟨k, ?_⟩
        rw [hcharge_k]
        exact Finset.mem_union_right _ (Finset.mem_union_right _ h)
  have hsold_pool_disj : ∀ {X : Finset G}, X ⊆ s.pool → Disjoint (s.sold \ s.own k) X := by
    intro X hX
    refine Finset.disjoint_left.mpr (fun x hx hxX => ?_)
    exact Finset.disjoint_left.mp (PStage.disjoint_pool_sold s) (hX hxX)
      (Finset.mem_sdiff.mp hx).1
  have hsoldsum : ∑ g ∈ s'.sold, p g = (∑ g ∈ s.sold, p g) - C + A + B := by
    rw [hsold, Finset.sum_union (hsold_pool_disj (Finset.union_subset hOpool hEpool)),
      Finset.sum_union hOE, Finset.sum_sdiff_eq_sub hownk_sold]
    ring
  -- ### monotonicity of the requirements
  have hreq_mono : ∀ j, s.req v p eps j ≤ s'.req v p eps j := by
    intro j
    by_cases hjk : j = k
    · subst hjk
      have h : s'.req v p eps j = vbarSum (v j) p S + q + eps := by
        simp [PStage.req, hserved', hbundle_k, hcash_k]
      rw [h]; linarith
    · by_cases hj : j ∈ s.served
      · have h1 : s.req v p eps j = vbarSum (v j) p (s.bundle j) + s.cash j + eps := by
          simp [PStage.req, hj]
        have h2 : s'.req v p eps j = vbarSum (v j) p (s.bundle j) + s.cash j + eps := by
          simp [PStage.req, hserved', Finset.mem_insert_of_mem hj, hbundle_ne j hjk,
            hcash_ne j hjk]
        rw [h1, h2]
      · have hj' : j ∉ insert k s.served := by
          simp only [Finset.mem_insert]; tauto
        have h1 : s.req v p eps j = GeneralTPS.thr v p j := by simp [PStage.req, hj]
        have h2 : s'.req v p eps j = GeneralTPS.thr v p j := by
          simp only [PStage.req, hserved']; rw [if_neg hj']
        rw [h1, h2]
  have hreq_ne : ∀ j, j ≠ k → s'.req v p eps j = s.req v p eps j := by
    intro j hjk
    by_cases hj : j ∈ s.served
    · simp [PStage.req, hserved', hj, Finset.mem_insert_of_mem hj, hbundle_ne j hjk,
        hcash_ne j hjk]
    · have hj' : j ∉ insert k s.served := by simp only [Finset.mem_insert]; tauto
      simp only [PStage.req, hserved']
      rw [if_neg hj', if_neg hj]
  -- ### the new owner is above its threshold
  have hthr : GeneralTPS.thr v p k ≤ vbarSum (v k) p S + q := by
    by_cases hk : k ∈ s.served
    · have h1 : s.req v p eps k = vbarSum (v k) p (s.bundle k) + s.cash k + eps := by
        simp [PStage.req, hk]
      have h2 := hs.share k hk
      rw [h1] at hclaim
      linarith
    · have h1 : s.req v p eps k = GeneralTPS.thr v p k := by simp [PStage.req, hk]
      rw [h1] at hclaim; exact hclaim
  refine ⟨s', ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- unserved agents hold nothing
    intro i hi
    have hik : i ≠ k := fun h => hi (by rw [h]; exact Finset.mem_insert_self _ _)
    have his : i ∉ s.served := fun h => hi (Finset.mem_insert_of_mem h)
    obtain ⟨h1, h2, h3, h4, h5⟩ := hs.unserved i his
    exact ⟨by rw [hbundle_ne i hik]; exact h1, by rw [hown_ne i hik]; exact h2,
      by rw [hext_ne i hik]; exact h3, by rw [hcash_ne i hik]; exact h4,
      by rw [hresv_ne i hik]; exact h5⟩
  · -- bundles are pairwise disjoint
    intro i j hij
    by_cases hi : i = k
    · subst hi
      rw [hbundle_k, hbundle_ne j (Ne.symm hij)]
      exact hpool_bundle hSpool j
    · by_cases hj : j = k
      · subst hj
        rw [hbundle_k, hbundle_ne i hi]
        exact (hpool_bundle hSpool i).symm
      · rw [hbundle_ne i hi, hbundle_ne j hj]
        exact hs.bundle_disj i j hij
  · -- sold goods are in nobody's bundle
    intro i j
    have hY : s'.bundle j = s.bundle j ∨ s'.bundle j = S := by
      by_cases hj : j = k
      · exact Or.inr (by rw [hj, hbundle_k])
      · exact Or.inl (hbundle_ne j hj)
    have hX : s'.charge i = s.charge i ∨ s'.charge i = S₀own ∪ (s.ext k ∪ S₀ext) := by
      by_cases hi : i = k
      · exact Or.inr (by rw [hi, hcharge_k])
      · exact Or.inl (hcharge_ne i hi)
    have hcS : Disjoint (s.charge i) S := (hpool_charge hSpool i).symm
    have hnewb : Disjoint (S₀own ∪ (s.ext k ∪ S₀ext)) (s.bundle j) := by
      refine Finset.disjoint_union_left.mpr ⟨hpool_bundle hOpool j, ?_⟩
      refine Finset.disjoint_union_left.mpr ⟨?_, hpool_bundle hEpool j⟩
      exact Finset.disjoint_of_subset_left Finset.subset_union_right (hs.charge_bundle k j)
    have hnewS : Disjoint (S₀own ∪ (s.ext k ∪ S₀ext)) S := by
      refine Finset.disjoint_union_left.mpr ⟨hSO.symm, ?_⟩
      exact Finset.disjoint_union_left.mpr ⟨(hpool_ext hSpool k).symm, hSE.symm⟩
    rcases hX with h | h <;> rcases hY with h' | h' <;> rw [h, h']
    · exact hs.charge_bundle i j
    · exact hcS
    · exact hnewb
    · exact hnewS
  · -- self-financed sales belong to one agent only
    intro i j hij
    by_cases hi : i = k
    · subst hi
      rw [hown_k, hown_ne j (Ne.symm hij)]
      exact hpool_own hOpool j
    · by_cases hj : j = k
      · subst hj
        rw [hown_k, hown_ne i hi]
        exact (hpool_own hOpool i).symm
      · rw [hown_ne i hi, hown_ne j hj]
        exact hs.own_disj i j hij
  · -- a self-financed sale is never a large-good sale
    intro i j
    by_cases hi : i = k
    · subst i
      by_cases hj : j = k
      · subst hj
        rw [hown_k, hext_k]
        exact Finset.disjoint_union_right.mpr ⟨hpool_ext hOpool _, hOE⟩
      · rw [hown_k, hext_ne j hj]
        exact hpool_ext hOpool j
    · by_cases hj : j = k
      · subst hj
        rw [hown_ne i hi, hext_k]
        exact Finset.disjoint_union_right.mpr ⟨hs.own_ext i _, (hpool_own hEpool i).symm⟩
      · rw [hown_ne i hi, hext_ne j hj]
        exact hs.own_ext i j
  · -- large-good sales are pure, or shared
    intro i g hg
    by_cases hi : i = k
    · subst i
      rw [hext_k] at hg
      rcases Finset.mem_union.mp hg with h | h
      · exact Or.inl (PureGood.mono (Finset.subset_insert k s.served) (hkpure g h))
      · rcases hpure with hp1 | ⟨hS, hO, hr0, g0, hE, hqg⟩
        · exact Or.inl (hp1 g h)
        · right
          have hgg : g = g0 := by rw [hE] at h; simpa using h
          subst hgg
          refine ⟨by rw [hbundle_k, hS], by rw [hown_k, hO], by rw [hresv_k, hr0],
            by rw [hcash_k]; exact hqg, ?_⟩
          intro g' hg' hne
          rw [hext_k, hE] at hg'
          rcases Finset.mem_union.mp hg' with h' | h'
          · exact PureGood.mono (Finset.subset_insert k s.served) (hkpure g' h')
          · exact absurd (Finset.mem_singleton.mp h') hne
    · rw [hext_ne i hi] at hg
      rcases hs.ext_ok i g hg with h | ⟨h1, h2, h3, h4, h5⟩
      · exact Or.inl (PureGood.mono (Finset.subset_insert k s.served) h)
      · right
        refine ⟨by rw [hbundle_ne i hi]; exact h1, by rw [hown_ne i hi]; exact h2,
          by rw [hresv_ne i hi]; exact h3, by rw [hcash_ne i hi]; exact h4, ?_⟩
        intro g' hg' hne
        rw [hext_ne i hi] at hg'
        exact PureGood.mono (Finset.subset_insert k s.served) (h5 g' hg' hne)
  · -- only pure large-good sales are charged to more than one agent
    intro i i' hii g hg hg'
    have hfresh : ∀ m, g ∈ S₀ext → g ∉ s.ext m := fun m hgX hgm =>
      Finset.disjoint_left.mp (hpool_ext hEpool m) hgX hgm
    by_cases hi : i = k
    · subst i
      rw [hext_k] at hg
      rw [hext_ne i' (Ne.symm hii)] at hg'
      rcases Finset.mem_union.mp hg with h | h
      · exact PureGood.mono (Finset.subset_insert k s.served) (hs.ext_uniq k i' hii g h hg')
      · exact absurd hg' (hfresh i' h)
    · by_cases hi' : i' = k
      · subst i'
        rw [hext_ne i hi] at hg
        rw [hext_k] at hg'
        rcases Finset.mem_union.mp hg' with h | h
        · exact PureGood.mono (Finset.subset_insert k s.served) (hs.ext_uniq i k hii g hg h)
        · exact absurd hg (hfresh i h)
      · rw [hext_ne i hi] at hg
        rw [hext_ne i' hi'] at hg'
        exact PureGood.mono (Finset.subset_insert k s.served) (hs.ext_uniq i i' hii g hg hg')
  · -- cash is non-negative
    intro i
    by_cases hi : i = k
    · subst hi; rw [hcash_k]; exact hq
    · rw [hcash_ne i hi]; exact hs.cash_nonneg i
  · -- the reserve is non-negative
    intro i
    by_cases hi : i = k
    · subst hi; rw [hresv_k]; exact hr
    · rw [hresv_ne i hi]; exact hs.resv_nonneg i
  · -- the bank is non-negative
    show (0:ℝ) ≤ s.bank + (s.cash k + s.resv k - C) + A + B - q - r
    linarith
  · -- self-financing
    intro i
    by_cases hi : i = k
    · subst hi; rw [hown_k, hcash_k, hresv_k]; exact hself
    · rw [hown_ne i hi, hcash_ne i hi, hresv_ne i hi]; exact hs.self_fin i
  · -- the money equation
    have hc : ∑ i, s'.cash i = ∑ i, s.cash i - s.cash k + q := by
      show ∑ i, Function.update s.cash k q i = _
      exact sum_update_eq s.cash k q
    have hrr : ∑ i, s'.resv i = ∑ i, s.resv i - s.resv k + r := by
      show ∑ i, Function.update s.resv k r i = _
      exact sum_update_eq s.resv k r
    have hbk : s'.bank = s.bank + (s.cash k + s.resv k - C) + A + B - q - r := rfl
    rw [hc, hrr, hbk, hsoldsum]
    have := hs.money
    linarith
  · -- every served agent is above its threshold
    intro i hi
    by_cases hik : i = k
    · subst hik
      rw [hbundle_k, hcash_k]; exact hthr
    · have his : i ∈ s.served := by
        rcases Finset.mem_insert.mp hi with h | h
        · exact absurd h hik
        · exact h
      rw [hbundle_ne i hik, hcash_ne i hik]
      exact hs.share i his
  · -- safety
    intro i hi j
    by_cases hik : i = k
    · subst i
      by_cases hjk : j = k
      · subst j
        left
        have h : s'.req v p eps k = vbarSum (v k) p S + q + eps := by
          simp [PStage.req, hserved', hbundle_k, hcash_k]
        rw [hbundle_k, hcash_k, h]; linarith
      · rcases hsafenew j hjk with h | ⟨h1, h2⟩
        · left; rw [hbundle_k, hcash_k, hreq_ne j hjk]; exact h
        · right
          refine ⟨by rw [hcash_k]; exact h1, ?_, ?_⟩
          · rw [hbundle_k]; exact hkeep
          · intro g hg
            rw [hbundle_k] at hg ⊢
            rw [hreq_ne j hjk]
            exact h2 g hg
    · have his : i ∈ s.served := by
        rcases Finset.mem_insert.mp hi with h | h
        · exact absurd h hik
        · exact h
      rcases hs.safe i his j with h | ⟨h1, h2, h3⟩
      · left
        rw [hbundle_ne i hik, hcash_ne i hik]
        exact le_trans h (hreq_mono j)
      · right
        refine ⟨by rw [hcash_ne i hik]; exact h1, ?_, ?_⟩
        · rw [hbundle_ne i hik]; exact h2
        · intro g hg
          rw [hbundle_ne i hik] at hg ⊢
          exact le_trans (h3 g hg) (hreq_mono j)
  · -- the cost bound
    intro i hi j hj
    have hjs : j ∉ s.served := fun h => hj (Finset.mem_insert_of_mem h)
    have hjk : j ≠ k := fun h => hj (by rw [h]; exact Finset.mem_insert_self _ _)
    have hE0 : ∑ g ∈ s.ext k, saleLoss (v j) p (TPS n (v j) p) g = 0 :=
      Finset.sum_eq_zero (fun g hg => hkpure g hg j hjs)
    have hdisjE : Disjoint (s.ext k) S₀ext := (hpool_ext hEpool k).symm
    have hcostk : s'.cost v p k j = truncBundle (v j) p (TPS n (v j) p) S + q + r
        + ∑ g ∈ S₀own, saleLoss (v j) p (TPS n (v j) p) g
        + ∑ g ∈ S₀ext, saleLoss (v j) p (TPS n (v j) p) g := by
      simp only [PStage.cost, hbundle_k, hcash_k, hresv_k, hown_k, hext_k,
        Finset.sum_union hdisjE, hE0]
      ring
    have hbound : s'.cost v p k j ≤ 2 * GeneralTPS.thr v p j := by
      rw [hcostk]
      rcases hpure with hp1 | ⟨hS, hO, hr0, g0, hE, hqg⟩
      · have hz : ∑ g ∈ S₀ext, saleLoss (v j) p (TPS n (v j) p) g = 0 :=
          Finset.sum_eq_zero (fun g hg => hp1 g hg j hj)
        rw [hz, add_zero]
        exact hcostnew j hj
      · subst hS; subst hO; subst hr0; subst hE
        have hreqj : s.req v p eps j = GeneralTPS.thr v p j := by simp [PStage.req, hjs]
        have hthrj : 0 ≤ GeneralTPS.thr v p j := GeneralTPS.thr_nonneg v p hn hp j
        have hqr : q ≤ GeneralTPS.thr v p j := by
          rcases hsafenew j hjk with h | ⟨h1, _⟩
          · rw [hreqj] at h; simpa [vbarSum] using h
          · rw [h1]; exact hthrj
        have hqT : q ≤ TPS n (v j) p := le_trans hqr (ChargeTPS.thr_le_TPS v p hn hp j)
        have h2 := ChargeTPS.cash_add_saleLoss_le (v j) p (TPS n (v j) p) g0 q hqg hqT
        have h3 := ChargeTPS.TPS_le_two_thr v p hn hp j
        simp only [truncBundle, Finset.sum_empty, Finset.sum_singleton]
        linarith
    by_cases hik : i = k
    · subst hik; exact hbound
    · have his : i ∈ s.served := by
        rcases Finset.mem_insert.mp hi with h | h
        · exact absurd h hik
        · exact h
      have : s'.cost v p i j = s.cost v p i j := by
        simp [PStage.cost, hbundle_ne i hik, hcash_ne i hik, hresv_ne i hik, hown_ne i hik,
          hext_ne i hik]
      rw [this]
      exact hs.cost_le i his j hjs
  · -- progress
    by_cases hk : k ∈ s.served
    · right
      have hcard : s.served.card = s'.served.card := by
        rw [hserved', Finset.insert_eq_self.mpr hk]
      refine ⟨hcard, ?_⟩
      have htot : s'.total v p = s.total v p
          - (vbarSum (v k) p (s.bundle k) + s.cash k) + (vbarSum (v k) p S + q) := by
        unfold PStage.total
        have h1 : ∀ i, vbarSum (v i) p (s'.bundle i) + s'.cash i
            = Function.update (fun i => vbarSum (v i) p (s.bundle i) + s.cash i) k
              (vbarSum (v k) p S + q) i := by
          intro i
          by_cases hi : i = k
          · subst hi; rw [hbundle_k, hcash_k]; simp
          · rw [hbundle_ne i hi, hcash_ne i hi, Function.update_of_ne hi]
        rw [Finset.sum_congr rfl (fun i _ => h1 i), sum_update_eq]
      have h2 : s.req v p eps k = vbarSum (v k) p (s.bundle k) + s.cash k + eps := by
        simp [PStage.req, hk]
      rw [h2] at hclaim
      rw [htot]; linarith
    · left
      rw [hserved', Finset.card_insert_of_notMem hk]
      omega
end FairSelling.PhaseTPS
