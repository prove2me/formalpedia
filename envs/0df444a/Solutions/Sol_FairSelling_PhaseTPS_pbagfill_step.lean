-- Prove2me | solution 1 for FairSelling.PhaseTPS.pbagfill_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:52:26.346797+00:00
-- url     : https://prove2.me/submissions/e3ee7224-3303-4658-ad5b-ff4f9b53c21d

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseStep
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Theorems.Thm_FairSelling_PhaseTPS_preq_nonneg
import Theorems.Thm_FairSelling_PhaseTPS_preq_eq_thr
import Theorems.Thm_FairSelling_CfgTPS_Qc_claimed
import Theorems.Thm_FairSelling_CfgTPS_cost_bound
import Theorems.Thm_FairSelling_CfgTPS_exists_min_adm
import Theorems.Thm_FairSelling_CfgTPS_truncBundle_add_le_two
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_ChargeTPS_TPS_le_two_thr
import Theorems.Thm_FairSelling_ChargeTPS_package_of_claimant
import Theorems.Thm_FairSelling_ChargeTPS_sum_saleLoss
import Theorems.Thm_FairSelling_ChargeTPS_thr_le_TPS
import Theorems.Thm_FairSelling_GeneralTPS_thr_nonneg
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bank
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bundle
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_cash
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_resv
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_served
import Theorems.Thm_FairSelling_PhaseTPS_pstep_assign_any
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_trunc_le_max
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
theorem _root_.solution (hcarrier : PCarrierReassign v p eps)
    (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : PStage G n} (hs : s.Good v p eps) {k0 : Fin n}
    {P : Finset G} (hPpool : P ⊆ s.pool)
    (hfeas : CfgTPS.Feas v p (s.req v p eps) k0 s.bank P ∅)
    (hcheap : ∀ g ∈ P, ∀ j, j ∉ s.served → p g ≤ 2 * GeneralTPS.thr v p j) :
    ∃ s' : PStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by
  classical
  obtain ⟨S, S₀, hUP, hdisj, hadm, hmin⟩ :=
    CfgTPS.exists_min_adm v p (s.req v p eps) k0 s.bank P hp hfeas
  obtain ⟨k, hclaim⟩ := CfgTPS.Qc_claimed v p (s.req v p eps) k0 S
  obtain ⟨S', S₀', q, hS'S, hS₀S₀', hfoot, hdisj', hq0, hqle, hclaim', hkeep, hsafe, hcosteq⟩ :=
    ChargeTPS.package_of_claimant v p (s.req v p eps) k0 s.bank hp hdisj hadm k hclaim
  have hreq0 : ∀ m, 0 ≤ s.req v p eps m := preq_nonneg v p eps hn hp heps hs
  have hbank : 0 ≤ s.bank := hs.bank_nonneg
  set A := ∑ x ∈ S₀', p x with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun x _ => hp x
  set r := max 0 (A - q) with hr
  have hr0 : 0 ≤ r := le_max_left _ _
  have hqr : q + r = max q A := by
    rcases le_or_gt A q with h | h
    · rw [hr, max_eq_left (by linarith : A - q ≤ 0), max_eq_left h, add_zero]
    · rw [hr, max_eq_right (by linarith : (0:ℝ) ≤ A - q), max_eq_right h.le]; ring
  have hS'P : S' ⊆ P :=
    Finset.Subset.trans (Finset.Subset.trans hS'S Finset.subset_union_left) hUP
  have hS₀'P : S₀' ⊆ P := fun x hx => hUP (hfoot ▸ Finset.mem_union_right S' hx)
  have hS'pool : S' ⊆ s.pool := Finset.Subset.trans hS'P hPpool
  have hS₀'pool : S₀' ⊆ s.pool := Finset.Subset.trans hS₀'P hPpool
  have hE : 0 ≤ s.cash k + s.resv k - ∑ x ∈ s.own k, p x := by
    have := hs.self_fin k; linarith
  refine pstep_assign_any v p eps hcarrier hn hp heps hs (S := S') (S₀own := S₀') (S₀ext := ∅)
    hS'pool hS₀'pool (by simp) hdisj' (by simp) (by simp) (q := q) (r := r) hq0 hr0 ?_ ?_
    (Or.inl (by simp)) hclaim' hkeep ?_ ?_
  · -- the package is affordable
    simp only [Finset.sum_empty, add_zero, ← hA]
    rw [hqr]
    rcases le_or_gt A q with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h.le]; linarith
  · -- the sales are self-financed
    rw [hqr, ← hA]
    exact le_max_right _ _
  · -- the package is safe for everybody
    intro j _
    exact hsafe j
  · -- the cost bound
    intro j hj
    have hjs : j ∉ s.served := fun h => hj (Finset.mem_insert_of_mem h)
    have hreqj : s.req v p eps j = GeneralTPS.thr v p j := preq_eq_thr v p eps hjs
    have hthrj : 0 ≤ GeneralTPS.thr v p j := GeneralTPS.thr_nonneg v p hn hp j
    rcases le_or_gt A q with hAq | hAq
    · -- the claimant draws money from the bank: the package costs what `Shrink` guarantees
      have hr0' : r = 0 := by rw [hr, max_eq_left (by linarith : A - q ≤ 0)]
      have hcost := CfgTPS.cost_bound (w := v) (p := p) (req := s.req v p eps) (k0 := k0)
        (D := s.bank) (P := P) (S := S) (S₀ := S₀)
        (fun i => TPS n (v i) p) j hp hbank hreq0
        (by rw [hreqj]; exact ChargeTPS.thr_le_TPS v p hn hp j)
        (by rw [hreqj]; exact ChargeTPS.TPS_le_two_thr v p hn hp j)
        hUP hdisj hadm hmin
      rw [hreqj] at hcost
      have heq := hcosteq (TPS n (v j) p) (v j)
      rw [hr0']
      linarith
    · -- the claimant keeps the whole proceeds of what it sells: the package costs its whole
      -- truncated footprint
      have hr0' : r = A - q := by rw [hr, max_eq_right (by linarith : (0:ℝ) ≤ A - q)]
      have hloss : ∑ x ∈ S₀', saleLoss (v j) p (TPS n (v j) p) x
          = truncBundle (v j) p (TPS n (v j) p) S₀' - A := ChargeTPS.sum_saleLoss _ _ _ _
      have hsplit : truncBundle (v j) p (TPS n (v j) p) S'
          + truncBundle (v j) p (TPS n (v j) p) S₀'
          = truncBundle (v j) p (TPS n (v j) p) (S ∪ S₀) := by
        rw [← hfoot]
        exact (Finset.sum_union hdisj').symm
      have hgoal : truncBundle (v j) p (TPS n (v j) p) S' + q + r
          + ∑ x ∈ S₀', saleLoss (v j) p (TPS n (v j) p) x
          = truncBundle (v j) p (TPS n (v j) p) (S ∪ S₀) := by
        rw [hloss, hr0', ← hsplit]; ring
      rw [hgoal]
      rcases le_or_gt 2 (S ∪ S₀).card with hcard | hcard
      · have h2 := CfgTPS.truncBundle_add_le_two (w := v) (req := s.req v p eps) (k0 := k0)
          (fun i => TPS n (v i) p) j hp hbank hUP hmin hcard
        rw [hreqj] at h2
        linarith
      · -- the footprint is a single sold good, and pool goods are cheap
        have hS₀ne : S₀'.Nonempty := by
          rcases Finset.eq_empty_or_nonempty S₀' with he | he
          · exfalso; rw [he] at hA; simp only [Finset.sum_empty] at hA; rw [hA] at hAq; linarith
          · exact he
        obtain ⟨x, hx⟩ := hS₀ne
        have hxU : x ∈ S ∪ S₀ := hfoot ▸ Finset.mem_union_right S' hx
        have hcard1 : (S ∪ S₀).card = 1 := by
          have : 1 ≤ (S ∪ S₀).card := Finset.card_pos.mpr ⟨x, hxU⟩
          omega
        obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcard1
        have hxy : x = y := by rw [hy] at hxU; simpa using hxU
        subst hxy
        have hxP : x ∈ P := hS₀'P hx
        have hpx : p x ≤ 2 * GeneralTPS.thr v p j := hcheap x hxP j hjs
        have htx : TPS n (v j) p ≤ 2 * GeneralTPS.thr v p j :=
          ChargeTPS.TPS_le_two_thr v p hn hp j
        have h1 : trunc (v j) p (TPS n (v j) p) x ≤ max (p x) (TPS n (v j) p) :=
          trunc_le_max _ _ _ _
        rw [hy]
        simp only [truncBundle, Finset.sum_singleton]
        rcases max_cases (p x) (TPS n (v j) p) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at h1 <;>
          linarith
end FairSelling.PhaseTPS
