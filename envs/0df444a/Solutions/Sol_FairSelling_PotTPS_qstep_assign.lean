-- Prove2me | solution 1 for FairSelling.PotTPS.qstep_assign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:52:57.856877+00:00
-- url     : https://prove2.me/submissions/77be2c42-9df8-49ae-8a8c-deb5c67935ef

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPot
import Definitions.Def_RequestProject_TPSSefxPotStep
import Theorems.Thm_FairSelling_PotTPS_sum_of_update
import Theorems.Thm_FairSelling_PotTPS_pot_of_update
import Theorems.Thm_FairSelling_ChargeTPS_CStage_disjoint_pool_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_PotTPS_QStage_cutSet_subset_sold
import Theorems.Thm_FairSelling_PotTPS_QStage_disjoint_pool_bundle
import Theorems.Thm_FairSelling_PotTPS_QStage_disjoint_pool_cutSet
import Theorems.Thm_FairSelling_PotTPS_QStage_disjoint_pool_own
import Theorems.Thm_FairSelling_PotTPS_QStage_disjoint_pool_sold
import Theorems.Thm_FairSelling_PotTPS_QStage_disjoint_pool_src
import Theorems.Thm_FairSelling_PotTPS_QStage_freeBank_nonneg_of
import Theorems.Thm_FairSelling_PotTPS_QStage_mem_cutSet
import Theorems.Thm_FairSelling_PotTPS_QStage_own_subset_sold
import Theorems.Thm_FairSelling_PotTPS_QStage_pot_of_pool
import Theorems.Thm_FairSelling_PotTPS_QStage_thr_le_req
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_bundle
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_cash
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_served
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_soldSet
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_P2M_FairSelling_PotTPS_QStage_cash_add_pot_le__f562961c4ebe
import Theorems.Thm_P2M_FairSelling_PotTPS_QStage_cost_le_of_src__1772b3ec5ee3
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.PotTPS.QStage.toStage_bundle
attribute [local simp] FairSelling.PotTPS.QStage.toStage_cash
attribute [local simp] FairSelling.PotTPS.QStage.toStage_served
attribute [local simp] FairSelling.PotTPS.QStage.toStage_soldSet
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
set_option maxHeartbeats 4000000
namespace FairSelling.PotTPS
theorem _root_.solution (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : QStage G n} (hs : s.Good v p eps) {k : Fin n}
    {S S₀ Src Snew : Finset G} {q r : ℝ}
    (hSpool : S ⊆ s.pool) (hS₀pool : S₀ ⊆ s.pool) (hSS₀ : Disjoint S S₀)
    (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hSrcCard : Src.card ≤ 1)
    (hSrcNe : Src ≠ ∅ → S = ∅ ∧ S₀ = ∅ ∧ r = 0)
    (hSnew : Snew = ∅ ∨ (Snew = Src ∧ Src ⊆ s.pool))
    (hSrcOld : Snew = ∅ → Src ⊆ s.cutSet)
    (hpotSrc : ∀ g ∈ Src, q ≤ s.pot p g)
    (hslice : Src ≠ ∅ → ∀ j, j ∉ s.served → q ≤ GeneralTPS.thr v p j)
    (hfin : Src = ∅ → q + r ≤ s.freeBank p + ∑ g ∈ S₀, p g)
    (hself : ∑ g ∈ S₀, p g ≤ q + r)
    (hclaim : s.req v p eps k ≤ vbarSum (v k) p S + q)
    (hkeep : ∀ g ∈ S, p g ≤ v k g)
    (hsafenew : ∀ j, j ≠ k → (vbarSum (v j) p S + q ≤ s.req v p eps j) ∨
      (q = 0 ∧ ∀ g ∈ S, vbarSum (v j) p (S \ {g}) + p g ≤ s.req v p eps j))
    (hcostnew : Src = ∅ → ∀ j, j ∉ insert k s.served →
      truncBundle (v j) p (TPS n (v j) p) S + q + r
        + ∑ g ∈ S₀, saleLoss (v j) p (TPS n (v j) p) g ≤ 2 * GeneralTPS.thr v p j) :
    ∃ s' : QStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by
  classical
  -- ### the released cut goods
  set RS : Finset G := (s.src k).filter (fun g => s.holders g = {k} ∧ g ∉ Src) with hRSdef
  set C : ℝ := ∑ g ∈ s.own k, p g with hCdef
  set R : ℝ := ∑ g ∈ RS, p g with hRdef
  set A : ℝ := ∑ g ∈ S₀, p g with hAdef
  set Bn : ℝ := ∑ g ∈ Snew, p g with hBndef
  set s' : QStage G n :=
    ⟨insert k s.served, Function.update s.bundle k S, Function.update s.own k S₀,
      Function.update s.src k Src, Function.update s.cash k q, Function.update s.resv k r,
      s.bank + s.cash k + s.resv k - C - R + A + Bn - q - r⟩ with hs'def
  -- ### the fields of the new state
  have hserved' : s'.served = insert k s.served := rfl
  have hbundle'k : s'.bundle k = S := by simp [hs'def]
  have hbundle'ne : ∀ i, i ≠ k → s'.bundle i = s.bundle i := fun i hi => by
    simp [hs'def, Function.update_of_ne hi]
  have hown'k : s'.own k = S₀ := by simp [hs'def]
  have hown'ne : ∀ i, i ≠ k → s'.own i = s.own i := fun i hi => by
    simp [hs'def, Function.update_of_ne hi]
  have hsrc'k : s'.src k = Src := by simp [hs'def]
  have hsrc'ne : ∀ i, i ≠ k → s'.src i = s.src i := fun i hi => by
    simp [hs'def, Function.update_of_ne hi]
  have hcash'k : s'.cash k = q := by simp [hs'def]
  have hcash'ne : ∀ i, i ≠ k → s'.cash i = s.cash i := fun i hi => by
    simp [hs'def, Function.update_of_ne hi]
  have hresv'k : s'.resv k = r := by simp [hs'def]
  have hresv'ne : ∀ i, i ≠ k → s'.resv i = s.resv i := fun i hi => by
    simp [hs'def, Function.update_of_ne hi]
  have hbank' : s'.bank = s.bank + s.cash k + s.resv k - C - R + A + Bn - q - r := rfl
  have hsrcfun : s'.src = Function.update s.src k Src := rfl
  have hcashfun : s'.cash = Function.update s.cash k q := rfl
  -- ### the pot of the new state
  have hpot' : ∀ g, s'.pot p g
      = s.pot p g + (if g ∈ s.src k then s.cash k else 0) - (if g ∈ Src then q else 0) :=
    pot_of_update p hsrcfun hcashfun
  have hcash'nonneg : ∀ i, 0 ≤ s'.cash i := by
    intro i
    by_cases hik : i = k
    · rw [hik, hcash'k]; exact hq
    · rw [hcash'ne i hik]; exact hs.cash_nonneg i
  have hresv'nonneg : ∀ i, 0 ≤ s'.resv i := by
    intro i
    by_cases hik : i = k
    · rw [hik, hresv'k]; exact hr
    · rw [hresv'ne i hik]; exact hs.resv_nonneg i
  -- ### basic facts about `RS`
  have hRSsub : RS ⊆ s.src k := Finset.filter_subset _ _
  have hRShold : ∀ x ∈ RS, s.holders x = {k} := fun x hx => ((Finset.mem_filter.mp hx).2).1
  have hRSSrc : ∀ x ∈ RS, x ∉ Src := fun x hx => ((Finset.mem_filter.mp hx).2).2
  have hRScut : RS ⊆ s.cutSet := fun x hx => QStage.mem_cutSet (hRSsub hx)
  have howncut : ∀ i, Disjoint (s.own i) s.cutSet := by
    intro i
    show Disjoint (s.own i) (Finset.univ.biUnion s.src)
    exact (Finset.disjoint_biUnion_right _ _ _).mpr (fun j _ => hs.own_cut i j)
  have hsolddef : s.sold = (Finset.univ.biUnion s.own) ∪ s.cutSet := rfl
  set OW : Finset G := Finset.univ.biUnion s.own with hOWdef
  have hOWsold : OW ⊆ s.sold := fun x hx => Finset.mem_union_left _ hx
  have hOWcut : Disjoint OW s.cutSet :=
    (Finset.disjoint_biUnion_left _ _ _).mpr (fun i _ => howncut i)
  have hcutsold : s.cutSet ⊆ s.sold := QStage.cutSet_subset_sold s
  -- ### the new sold set
  have hOW' : Finset.univ.biUnion s'.own = (OW \ s.own k) ∪ S₀ := by
    ext x
    simp only [hOWdef, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_sdiff]
    constructor
    · rintro ⟨i, hi⟩
      by_cases hik : i = k
      · rw [hik] at hi; right; rwa [hown'k] at hi
      · rw [hown'ne i hik] at hi
        exact Or.inl ⟨⟨i, hi⟩, fun hc => Finset.disjoint_left.mp (hs.own_disj i k hik) hi hc⟩
    · rintro (⟨⟨i, hi⟩, hx⟩ | hx)
      · have hik : i ≠ k := fun h => hx (h ▸ hi)
        exact ⟨i, by rw [hown'ne i hik]; exact hi⟩
      · exact ⟨k, by rw [hown'k]; exact hx⟩
  have hcut' : s'.cutSet = (s.cutSet \ RS) ∪ Src := by
    ext x
    simp only [QStage.cutSet, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_sdiff]
    constructor
    · rintro ⟨i, hi⟩
      by_cases hik : i = k
      · rw [hik] at hi; right; rwa [hsrc'k] at hi
      · rw [hsrc'ne i hik] at hi
        refine Or.inl ⟨⟨i, hi⟩, fun hx => ?_⟩
        have h1 : i ∈ s.holders x := by simp [QStage.holders, hi]
        rw [hRShold x hx] at h1
        exact hik (Finset.mem_singleton.mp h1)
    · rintro (⟨⟨i, hi⟩, hx⟩ | hx)
      · by_cases hik : i = k
        · rw [hik] at hi
          by_cases hxS : x ∈ Src
          · exact ⟨k, by rw [hsrc'k]; exact hxS⟩
          · have hnot : ¬ (s.holders x = {k} ∧ x ∉ Src) := fun hc =>
              hx (Finset.mem_filter.mpr ⟨hi, hc⟩)
            have hne : s.holders x ≠ {k} := fun hc => hnot ⟨hc, hxS⟩
            have hkmem : k ∈ s.holders x := by simp [QStage.holders, hi]
            obtain ⟨i', hi', hne'⟩ : ∃ i' ∈ s.holders x, i' ≠ k := by
              by_contra hcon
              push_neg at hcon
              exact hne (Finset.Subset.antisymm
                (fun y hy => Finset.mem_singleton.mpr (hcon y hy))
                (Finset.singleton_subset_iff.mpr hkmem))
            refine ⟨i', ?_⟩
            rw [hsrc'ne i' hne']
            simpa [QStage.holders] using hi'
        · exact ⟨i, by rw [hsrc'ne i hik]; exact hi⟩
      · exact ⟨k, by rw [hsrc'k]; exact hx⟩
  set T : Finset G := s.sold \ (s.own k ∪ RS) with hTdef
  have hT_eq : T = (OW \ s.own k) ∪ (s.cutSet \ RS) := by
    rw [hTdef, hsolddef]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl ⟨h1, fun hc => h2 (Or.inl hc)⟩
      · exact Or.inr ⟨h1, fun hc => h2 (Or.inr hc)⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · refine ⟨Or.inl h1, ?_⟩
        rintro (hc | hc)
        · exact h2 hc
        · exact Finset.disjoint_left.mp hOWcut h1 (hRScut hc)
      · refine ⟨Or.inr h1, ?_⟩
        rintro (hc | hc)
        · exact Finset.disjoint_left.mp (howncut k) hc h1
        · exact h2 hc
  have hSnewPool : Snew ⊆ s.pool := by
    rcases hSnew with h | ⟨h1, h2⟩
    · rw [h]; exact Finset.empty_subset _
    · rw [h1]; exact h2
  have hSrcT : Snew = ∅ → Src ⊆ s.cutSet \ RS := by
    intro h x hx
    exact Finset.mem_sdiff.mpr ⟨hSrcOld h hx, fun hc => hRSSrc x hc hx⟩
  have hsold' : s'.sold = T ∪ S₀ ∪ Snew := by
    have hbase : s'.sold = (Finset.univ.biUnion s'.own) ∪ s'.cutSet := rfl
    rw [hbase, hOW', hcut', hT_eq]
    rcases hSnew with h | ⟨h1, _⟩
    · have hsub := hSrcT h
      rw [h, Finset.union_empty, Finset.union_eq_left.mpr hsub]
      exact (Finset.union_right_comm _ _ _).symm
    · rw [h1]
      ext x
      simp only [Finset.mem_union]
      tauto
  -- ### the money
  have hownRSsold : s.own k ∪ RS ⊆ s.sold := by
    refine Finset.union_subset (QStage.own_subset_sold s k) ?_
    exact fun x hx => hcutsold (hRScut hx)
  have hownRSdisj : Disjoint (s.own k) RS :=
    Finset.disjoint_of_subset_right (fun x hx => hRScut hx) (howncut k)
  have hTsum : ∑ g ∈ T, p g = ∑ g ∈ s.sold, p g - C - R := by
    rw [hTdef, Finset.sum_sdiff_eq_sub hownRSsold, Finset.sum_union hownRSdisj, hCdef, hRdef]
    ring
  have hTsold : T ⊆ s.sold := Finset.sdiff_subset
  have hTS₀ : Disjoint T S₀ :=
    Finset.disjoint_of_subset_left hTsold
      (Finset.disjoint_of_subset_right hS₀pool (Disjoint.symm (QStage.disjoint_pool_sold s)))
  have hTSnew : Disjoint T Snew :=
    Finset.disjoint_of_subset_left hTsold
      (Finset.disjoint_of_subset_right hSnewPool (Disjoint.symm (QStage.disjoint_pool_sold s)))
  have hS₀Snew : Disjoint S₀ Snew := by
    rcases hSnew with h | ⟨h1, _⟩
    · rw [h]; exact Finset.disjoint_empty_right _
    · rcases Finset.eq_empty_or_nonempty Src with hE | hE
      · rw [h1, hE]; exact Finset.disjoint_empty_right _
      · have := (hSrcNe (Finset.nonempty_iff_ne_empty.mp hE)).2.1
        rw [this]; exact Finset.disjoint_empty_left _
  have hsoldsum : ∑ g ∈ s'.sold, p g = ∑ g ∈ s.sold, p g - C - R + A + Bn := by
    rw [hsold', Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hTSnew, hS₀Snew⟩),
      Finset.sum_union hTS₀, hTsum, hAdef, hBndef]
  -- ### the free bank after the release
  set SigC : ℝ := ∑ g ∈ s.cutSet, s.pot p g with hSigCdef
  have hfreeeq : s.freeBank p = s.bank - SigC := rfl
  have hfree0 : 0 ≤ s.freeBank p := QStage.freeBank_nonneg_of hs
  set potR : G → ℝ := fun g => s.pot p g + (if g ∈ s.src k then s.cash k else 0) with hpotRdef
  have hDelta : s.freeBank p + ∑ g ∈ s.cutSet \ RS, potR g
      ≤ s.bank + s.cash k + s.resv k - C - R := by
    rcases Finset.eq_empty_or_nonempty (s.src k) with hsk | hsk
    · have hRSempty : RS = ∅ := by
        rw [hRSdef, hsk]; simp
      have hR0 : R = 0 := by rw [hRdef, hRSempty]; simp
      have hsum : ∑ g ∈ s.cutSet \ RS, potR g = SigC := by
        rw [hRSempty, Finset.sdiff_empty, hSigCdef]
        refine Finset.sum_congr rfl (fun g _ => ?_)
        simp [hpotRdef, hsk]
      have hsf := hs.self_fin k
      rw [hsum, hfreeeq, hR0]
      linarith
    · obtain ⟨g1, hg1⟩ : ∃ g1, s.src k = {g1} := by
        have h1 := hs.src_card k
        have h2 : 1 ≤ (s.src k).card := Finset.card_pos.mpr hsk
        exact Finset.card_eq_one.mp (by omega)
      obtain ⟨hbk, hok, hrk⟩ := hs.cutter k (Finset.nonempty_iff_ne_empty.mp hsk)
      have hC0 : C = 0 := by rw [hCdef, hok]; simp
      have hg1cut : g1 ∈ s.cutSet := QStage.mem_cutSet (by rw [hg1]; simp)
      by_cases hcase : s.holders g1 = {k} ∧ g1 ∉ Src
      · have hRSeq : RS = {g1} := by
          rw [hRSdef, hg1]
          simp [hcase]
        have hR1 : R = p g1 := by rw [hRdef, hRSeq]; simp
        have hpotg1 : s.pot p g1 = p g1 - s.cash k := by
          simp [QStage.pot, hcase.1]
        have hsum : ∑ g ∈ s.cutSet \ RS, potR g = SigC - s.pot p g1 := by
          rw [hRSeq, hSigCdef]
          rw [show ∑ g ∈ s.cutSet \ {g1}, potR g = ∑ g ∈ s.cutSet \ {g1}, s.pot p g from
            Finset.sum_congr rfl (fun g hg => by
              have : g ≠ g1 := by
                intro hgg; exact (Finset.mem_sdiff.mp hg).2 (by simp [hgg])
              simp [hpotRdef, hg1, this])]
          rw [Finset.sum_sdiff_eq_sub (Finset.singleton_subset_iff.mpr hg1cut)]
          simp
        rw [hsum, hfreeeq, hC0, hR1, hrk, hpotg1]
        ring_nf
        linarith
      · have hRSeq : RS = ∅ := by
          rw [hRSdef, hg1]
          simp only [Finset.filter_singleton, if_neg hcase]
        have hR0 : R = 0 := by rw [hRdef, hRSeq]; simp
        have hsum : ∑ g ∈ s.cutSet \ RS, potR g = SigC + s.cash k := by
          rw [hRSeq, Finset.sdiff_empty, hSigCdef, hpotRdef]
          rw [Finset.sum_add_distrib]
          congr 1
          rw [show ∑ g ∈ s.cutSet, (if g ∈ s.src k then s.cash k else 0)
              = ∑ g ∈ s.cutSet, (if g = g1 then s.cash k else 0) from
            Finset.sum_congr rfl (fun g _ => by simp [hg1])]
          rw [Finset.sum_ite_eq' s.cutSet g1 (fun _ => s.cash k)]
          simp [hg1cut]
        rw [hsum, hfreeeq, hC0, hR0, hrk]
        linarith
    -- end of hDelta
  -- ### the shape of `Src`
  have hSrcCases : Src = ∅ ∨ ∃ g0, Src = {g0} := by
    rcases Finset.eq_empty_or_nonempty Src with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.card_eq_one.mp (by
        have := Finset.card_pos.mpr h; omega))
  -- ### the new bank covers the new pots
  have hbankpot' : ∑ g ∈ s'.cutSet, s'.pot p g ≤ s'.bank := by
    rcases hSrcCases with hE | ⟨g0, hE⟩
    · -- no slice is handed out
      have hSnewE : Snew = ∅ := by
        rcases hSnew with h | ⟨h1, _⟩
        · exact h
        · rw [h1, hE]
      have hBn0 : Bn = 0 := by rw [hBndef, hSnewE]; simp
      have hcutE : s'.cutSet = s.cutSet \ RS := by rw [hcut', hE]; simp
      have hsum : ∑ g ∈ s'.cutSet, s'.pot p g = ∑ g ∈ s.cutSet \ RS, potR g := by
        rw [hcutE]
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [hpot', hE]
        simp [hpotRdef]
      rw [hsum, hbank', hBn0]
      have := hfin hE
      linarith
    · have hSne : Src ≠ ∅ := by rw [hE]; simp
      obtain ⟨hSE, hS₀E, hrE⟩ := hSrcNe hSne
      have hA0 : A = 0 := by rw [hAdef, hS₀E]; simp
      rcases hSnew with hSnewE | ⟨h1, h2⟩
      · -- the slice is cut out of a pot that already exists
        have hBn0 : Bn = 0 := by rw [hBndef, hSnewE]; simp
        have hg0T : g0 ∈ s.cutSet \ RS := hSrcT hSnewE (by rw [hE]; simp)
        have hcutE : s'.cutSet = s.cutSet \ RS := by
          rw [hcut', hE]
          exact Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr hg0T)
        have hsum : ∑ g ∈ s'.cutSet, s'.pot p g = (∑ g ∈ s.cutSet \ RS, potR g) - q := by
          rw [hcutE]
          have hstep : ∀ g ∈ s.cutSet \ RS, s'.pot p g = potR g - (if g = g0 then q else 0) := by
            intro g _
            rw [hpot', hE]; simp [hpotRdef]
          rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib,
            Finset.sum_ite_eq' (s.cutSet \ RS) g0 (fun _ => q), if_pos hg0T]
        rw [hsum, hbank', hA0, hBn0, hrE]
        linarith
      · -- a fresh good is sold and cut
        have hg0pool : g0 ∈ s.pool := h2 (by rw [hE]; simp)
        have hBn : Bn = p g0 := by rw [hBndef, h1, hE]; simp
        have hg0notcut : g0 ∉ s.cutSet := fun hc =>
          Finset.disjoint_left.mp (QStage.disjoint_pool_cutSet s) hg0pool hc
        have hg0notsrck : g0 ∉ s.src k := fun hc => hg0notcut (QStage.mem_cutSet hc)
        have hpotg0 : s.pot p g0 = p g0 := QStage.pot_of_pool hg0pool
        have hdisjg0 : Disjoint (s.cutSet \ RS) ({g0} : Finset G) := by
          refine Finset.disjoint_singleton_right.mpr (fun hc => hg0notcut (Finset.mem_sdiff.mp hc).1)
        have hcutE : s'.cutSet = (s.cutSet \ RS) ∪ {g0} := by rw [hcut', hE]
        have hsum : ∑ g ∈ s'.cutSet, s'.pot p g
            = (∑ g ∈ s.cutSet \ RS, potR g) + (p g0 - q) := by
          rw [hcutE, Finset.sum_union hdisjg0]
          congr 1
          · refine Finset.sum_congr rfl (fun g hg => ?_)
            have hgne : g ≠ g0 := fun hgg => hg0notcut (hgg ▸ (Finset.mem_sdiff.mp hg).1)
            rw [hpot', hE]
            simp [hpotRdef, hgne]
          · rw [Finset.sum_singleton, hpot', hE]
            simp [hg0notsrck, hpotg0]
        rw [hsum, hbank', hA0, hBn, hrE]
        linarith
  -- ### the pots are non-negative
  have hpotnonneg' : ∀ g ∈ s'.cutSet, 0 ≤ s'.pot p g := by
    intro g hg
    rw [hpot']
    have h1 : 0 ≤ (if g ∈ s.src k then s.cash k else 0) := by
      by_cases h : g ∈ s.src k <;> simp [h, hs.cash_nonneg k]
    by_cases hgS : g ∈ Src
    · have := hpotSrc g hgS
      simp only [hgS, if_pos]
      linarith
    · rw [if_neg hgS]
      have hgc : g ∈ s.cutSet := by
        rw [hcut'] at hg
        rcases Finset.mem_union.mp hg with h | h
        · exact (Finset.mem_sdiff.mp h).1
        · exact absurd h hgS
      have := hs.pot_nonneg g hgc
      linarith
  -- ### monotonicity of the requirement
  have hclaimthr : GeneralTPS.thr v p k ≤ vbarSum (v k) p S + q :=
    le_trans (QStage.thr_le_req heps hs k) hclaim
  have hreqmono : ∀ j, s.req v p eps j ≤ s'.req v p eps j := by
    intro j
    by_cases hjk : j = k
    · subst hjk
      have : s'.req v p eps j = vbarSum (v j) p S + q + eps := by
        simp [QStage.req, hserved', hbundle'k, hcash'k]
      rw [this]; linarith
    · by_cases hj : j ∈ s.served
      · have h1 : s'.req v p eps j = vbarSum (v j) p (s.bundle j) + s.cash j + eps := by
          simp [QStage.req, hserved', Finset.mem_insert_of_mem hj, hbundle'ne j hjk,
            hcash'ne j hjk]
        have h2 : s.req v p eps j = vbarSum (v j) p (s.bundle j) + s.cash j + eps := by
          simp [QStage.req, hj]
        rw [h1, h2]
      · have hj' : j ∉ insert k s.served := by
          simp only [Finset.mem_insert]
          push_neg
          exact ⟨hjk, hj⟩
        have h1 : s'.req v p eps j = GeneralTPS.thr v p j := by
          simp [QStage.req, hserved', hj']
        have h2 : s.req v p eps j = GeneralTPS.thr v p j := by simp [QStage.req, hj]
        rw [h1, h2]
  -- ### the invariant
  have hgood : s'.Good v p eps := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hcash'nonneg, hresv'nonneg, hpotnonneg', hbankpot',
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- unserved
      intro i hi
      have hik : i ≠ k := fun h => hi (by rw [hserved', h]; exact Finset.mem_insert_self _ _)
      have hi' : i ∉ s.served := fun h => hi (by rw [hserved']; exact Finset.mem_insert_of_mem h)
      obtain ⟨h1, h2, h3, h4, h5⟩ := hs.unserved i hi'
      exact ⟨by rw [hbundle'ne i hik, h1], by rw [hown'ne i hik, h2],
        by rw [hsrc'ne i hik, h3], by rw [hcash'ne i hik, h4], by rw [hresv'ne i hik, h5]⟩
    · -- bundle_disj
      intro i j hij
      by_cases hik : i = k
      · subst hik
        rw [hbundle'k, hbundle'ne j (Ne.symm hij)]
        exact Finset.disjoint_of_subset_left hSpool (QStage.disjoint_pool_bundle s j)
      · by_cases hjk : j = k
        · subst hjk
          rw [hbundle'k, hbundle'ne i hik]
          exact Disjoint.symm (Finset.disjoint_of_subset_left hSpool
            (QStage.disjoint_pool_bundle s i))
        · rw [hbundle'ne i hik, hbundle'ne j hjk]
          exact hs.bundle_disj i j hij
    · -- sold_bundle
      intro i
      rw [hsold']
      refine Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨?_, ?_⟩, ?_⟩
      · by_cases hik : i = k
        · subst hik
          rw [hbundle'k]
          exact Finset.disjoint_of_subset_left hTsold
            (Disjoint.symm (Finset.disjoint_of_subset_left hSpool
              (QStage.disjoint_pool_sold s)))
        · rw [hbundle'ne i hik]
          exact Finset.disjoint_of_subset_left hTsold (hs.sold_bundle i)
      · by_cases hik : i = k
        · subst hik; rw [hbundle'k]; exact Disjoint.symm hSS₀
        · rw [hbundle'ne i hik]
          exact Finset.disjoint_of_subset_left hS₀pool (QStage.disjoint_pool_bundle s i)
      · by_cases hik : i = k
        · subst hik
          rw [hbundle'k]
          rcases Finset.eq_empty_or_nonempty Snew with h | h
          · rw [h]; exact Finset.disjoint_empty_left _
          · have hSrcne : Src ≠ ∅ := by
              rcases hSnew with h1 | ⟨h1, _⟩
              · exact absurd h1 (Finset.nonempty_iff_ne_empty.mp h)
              · rw [← h1]; exact Finset.nonempty_iff_ne_empty.mp h
            rw [(hSrcNe hSrcne).1]
            exact Finset.disjoint_empty_right _
        · rw [hbundle'ne i hik]
          exact Finset.disjoint_of_subset_left hSnewPool (QStage.disjoint_pool_bundle s i)
    · -- own_disj
      intro i j hij
      by_cases hik : i = k
      · subst hik
        rw [hown'k, hown'ne j (Ne.symm hij)]
        exact Finset.disjoint_of_subset_left hS₀pool (QStage.disjoint_pool_own s j)
      · by_cases hjk : j = k
        · subst hjk
          rw [hown'k, hown'ne i hik]
          exact Disjoint.symm (Finset.disjoint_of_subset_left hS₀pool
            (QStage.disjoint_pool_own s i))
        · rw [hown'ne i hik, hown'ne j hjk]
          exact hs.own_disj i j hij
    · -- own_cut
      intro i j
      by_cases hjk : j = k
      · rw [hjk, hsrc'k]
        by_cases hik : i = k
        · rw [hik, hown'k]
          rcases Finset.eq_empty_or_nonempty Src with h | h
          · rw [h]; exact Finset.disjoint_empty_right _
          · rw [(hSrcNe (Finset.nonempty_iff_ne_empty.mp h)).2.1]
            exact Finset.disjoint_empty_left _
        · rw [hown'ne i hik]
          rcases hSnew with h | ⟨_, h2⟩
          · exact Finset.disjoint_of_subset_right (hSrcOld h) (howncut i)
          · exact Finset.disjoint_of_subset_right h2 (Disjoint.symm
              (QStage.disjoint_pool_own s i))
      · rw [hsrc'ne j hjk]
        by_cases hik : i = k
        · subst hik
          rw [hown'k]
          exact Finset.disjoint_of_subset_left hS₀pool (QStage.disjoint_pool_src s j)
        · rw [hown'ne i hik]
          exact hs.own_cut i j
    · -- src_card
      intro i
      by_cases hik : i = k
      · subst hik; rw [hsrc'k]; exact hSrcCard
      · rw [hsrc'ne i hik]; exact hs.src_card i
    · -- cutter
      intro i hi
      by_cases hik : i = k
      · subst hik
        rw [hsrc'k] at hi
        obtain ⟨h1, h2, h3⟩ := hSrcNe hi
        exact ⟨by rw [hbundle'k, h1], by rw [hown'k, h2], by rw [hresv'k, h3]⟩
      · rw [hsrc'ne i hik] at hi
        obtain ⟨h1, h2, h3⟩ := hs.cutter i hi
        exact ⟨by rw [hbundle'ne i hik, h1], by rw [hown'ne i hik, h2],
          by rw [hresv'ne i hik, h3]⟩
    · -- self_fin
      intro i
      by_cases hik : i = k
      · subst hik
        rw [hown'k, hcash'k, hresv'k]
        exact hself
      · rw [hown'ne i hik, hcash'ne i hik, hresv'ne i hik]
        exact hs.self_fin i
    · -- money
      have h1 : ∑ i, s'.cash i = ∑ i, s.cash i - s.cash k + q := by
        rw [sum_of_update s.cash (fun i => s'.cash i) k (fun i hi => hcash'ne i hi), hcash'k]
      have h2 : ∑ i, s'.resv i = ∑ i, s.resv i - s.resv k + r := by
        rw [sum_of_update s.resv (fun i => s'.resv i) k (fun i hi => hresv'ne i hi), hresv'k]
      rw [h1, h2, hbank', hsoldsum, ← hs.money]
      ring
    · -- share
      intro i hi
      rw [hserved'] at hi
      rcases Finset.mem_insert.mp hi with hik | hi'
      · subst hik
        rw [hbundle'k, hcash'k]
        exact hclaimthr
      · have hik : i ≠ k ∨ i = k := ne_or_eq i k
        rcases hik with hik | hik
        · rw [hbundle'ne i hik, hcash'ne i hik]
          exact hs.share i hi'
        · subst hik
          rw [hbundle'k, hcash'k]
          exact hclaimthr
    · -- safe
      intro i hi j
      rw [hserved'] at hi
      by_cases hik : i = k
      · rw [hik]
        by_cases hjk : j = k
        · rw [hjk]
          left
          rw [hbundle'k, hcash'k]
          have hrq : s'.req v p eps k = vbarSum (v k) p S + q + eps := by
            simp [QStage.req, hserved', hbundle'k, hcash'k]
          rw [hrq]; linarith
        · rcases hsafenew j hjk with h | ⟨h1, h2⟩
          · left
            rw [hbundle'k, hcash'k]
            exact le_trans h (hreqmono j)
          · right
            refine ⟨by rw [hcash'k]; exact h1, ?_, ?_⟩
            · rw [hbundle'k]
              intro g hg
              exact hkeep g hg
            · rw [hbundle'k]
              intro g hg
              exact le_trans (h2 g hg) (hreqmono j)
      · have hi' : i ∈ s.served := by
          rcases Finset.mem_insert.mp hi with h | h
          · exact absurd h hik
          · exact h
        rcases hs.safe i hi' j with h | ⟨h1, h2, h3⟩
        · left
          rw [hbundle'ne i hik, hcash'ne i hik]
          exact le_trans h (hreqmono j)
        · right
          refine ⟨by rw [hcash'ne i hik]; exact h1, ?_, ?_⟩
          · rw [hbundle'ne i hik]; exact h2
          · rw [hbundle'ne i hik]
            intro g hg
            exact le_trans (h3 g hg) (hreqmono j)
    · -- cost_le
      intro i hi j hj
      rw [hserved'] at hi hj
      have hjk : j ≠ k := fun h => hj (by rw [h]; exact Finset.mem_insert_self _ _)
      have hjs : j ∉ s.served := fun h => hj (Finset.mem_insert_of_mem h)
      by_cases hik : i = k
      · subst hik
        rcases hSrcCases with hE | ⟨g0, hE⟩
        · have hcE : s'.cost v p i j
              = truncBundle (v j) p (TPS n (v j) p) S + q + r
                + ∑ g ∈ S₀, saleLoss (v j) p (TPS n (v j) p) g := by
            simp [QStage.cost, hbundle'k, hcash'k, hresv'k, hown'k, hsrc'k, hE]
          rw [hcE]
          exact hcostnew hE j hj
        · have hSne : Src ≠ ∅ := by rw [hE]; simp
          obtain ⟨hSE, hS₀E, hrE⟩ := hSrcNe hSne
          refine QStage.cost_le_of_src' hn hp (g := g0)
            (by rw [hbundle'k, hSE]) (by rw [hown'k, hS₀E]) (by rw [hresv'k, hrE])
            (by rw [hsrc'k, hE]) ?_ ?_
          · exact QStage.cash_add_pot_le' hcash'nonneg (by rw [hsrc'k, hE]; simp)
          · rw [hcash'k]
            exact hslice hSne j hjs
      · have hi' : i ∈ s.served := by
          rcases Finset.mem_insert.mp hi with h | h
          · exact absurd h hik
          · exact h
        rcases Finset.eq_empty_or_nonempty (s.src i) with hsi | hsi
        · have hcE : s'.cost v p i j = s.cost v p i j := by
            simp [QStage.cost, hbundle'ne i hik, hcash'ne i hik, hresv'ne i hik,
              hown'ne i hik, hsrc'ne i hik, hsi]
          rw [hcE]
          exact hs.cost_le i hi' j hjs
        · obtain ⟨g1, hg1⟩ : ∃ g1, s.src i = {g1} := by
            have h1 := hs.src_card i
            have h2 : 1 ≤ (s.src i).card := Finset.card_pos.mpr hsi
            exact Finset.card_eq_one.mp (by omega)
          obtain ⟨hb1, ho1, hr1⟩ := hs.cutter i (Finset.nonempty_iff_ne_empty.mp hsi)
          refine QStage.cost_le_of_src' hn hp (g := g1)
            (by rw [hbundle'ne i hik, hb1]) (by rw [hown'ne i hik, ho1])
            (by rw [hresv'ne i hik, hr1]) (by rw [hsrc'ne i hik, hg1]) ?_ ?_
          · exact QStage.cash_add_pot_le' hcash'nonneg (by rw [hsrc'ne i hik, hg1]; simp)
          · rw [hcash'ne i hik]
            exact hs.slice_le i (Finset.nonempty_iff_ne_empty.mp hsi) j hjs
    · -- slice_le
      intro i hi j hj
      rw [hserved'] at hj
      have hjs : j ∉ s.served := fun h => hj (Finset.mem_insert_of_mem h)
      by_cases hik : i = k
      · subst hik
        rw [hsrc'k] at hi
        rw [hcash'k]
        exact hslice hi j hjs
      · rw [hsrc'ne i hik] at hi
        rw [hcash'ne i hik]
        exact hs.slice_le i hi j hjs
  refine ⟨s', hgood, ?_⟩
  by_cases hkserved : k ∈ s.served
  · right
    refine ⟨by rw [hserved', Finset.insert_eq_self.mpr hkserved], ?_⟩
    have hne : ∀ i, i ≠ k → vbarSum (v i) p (s'.bundle i) + s'.cash i
        = vbarSum (v i) p (s.bundle i) + s.cash i := by
      intro i hi; rw [hbundle'ne i hi, hcash'ne i hi]
    have htot := sum_of_update (fun i => vbarSum (v i) p (s.bundle i) + s.cash i)
        (fun i => vbarSum (v i) p (s'.bundle i) + s'.cash i) k hne
    simp only [hbundle'k, hcash'k] at htot
    have hreqk : s.req v p eps k = vbarSum (v k) p (s.bundle k) + s.cash k + eps := by
      simp [QStage.req, hkserved]
    rw [hreqk] at hclaim
    show s.total v p + eps ≤ s'.total v p
    have e1 : s'.total v p = ∑ i, (vbarSum (v i) p (s'.bundle i) + s'.cash i) := rfl
    have e2 : s.total v p = ∑ i, (vbarSum (v i) p (s.bundle i) + s.cash i) := rfl
    rw [e1, e2, htot]
    linarith
  · left
    rw [hserved', Finset.card_insert_of_notMem hkserved]
    omega
end FairSelling.PotTPS
