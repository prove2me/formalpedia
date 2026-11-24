-- Prove2me | solution 1 for FairSelling.PotTPS.qbagfill_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:59:33.885322+00:00
-- url     : https://prove2.me/submissions/c8f5ed17-1dcc-4542-9109-17717848bcde

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPotStep
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPotImp
import Theorems.Thm_FairSelling_CfgTPS_Qc_claimed
import Theorems.Thm_FairSelling_CfgTPS_cost_bound
import Theorems.Thm_FairSelling_CfgTPS_exists_min_adm
import Theorems.Thm_FairSelling_CfgTPS_truncBundle_add_le_two
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_ChargeTPS_TPS_le_two_thr
import Theorems.Thm_FairSelling_ChargeTPS_package_of_claimant
import Theorems.Thm_FairSelling_ChargeTPS_req_eq_thr
import Theorems.Thm_FairSelling_ChargeTPS_req_nonneg
import Theorems.Thm_FairSelling_ChargeTPS_sum_saleLoss
import Theorems.Thm_FairSelling_ChargeTPS_thr_le_TPS
import Theorems.Thm_FairSelling_GeneralTPS_thr_nonneg
import Theorems.Thm_FairSelling_PotTPS_QStage_freeBank_nonneg_of
import Theorems.Thm_FairSelling_PotTPS_QStage_req_eq_thr
import Theorems.Thm_FairSelling_PotTPS_QStage_req_nonneg
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_bundle
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_cash
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_served
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_soldSet
import Theorems.Thm_FairSelling_PotTPS_qstep_assign
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_trunc_le_max
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
namespace FairSelling.PotTPS
theorem _root_.solution (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : QStage G n} (hs : s.Good v p eps) {k0 : Fin n}
    (hfeas : CfgTPS.Feas v p (s.req v p eps) k0 (s.freeBank p) s.pool ∅)
    (hcheap : ∀ g ∈ s.pool, ∀ j, j ∉ s.served → p g ≤ 2 * GeneralTPS.thr v p j) :
    ∃ s' : QStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by
  classical
  set D : ℝ := s.freeBank p with hDdef
  obtain ⟨S, S₀, hUP, hdisj, hadm, hmin⟩ :=
    CfgTPS.exists_min_adm v p (s.req v p eps) k0 D s.pool hp hfeas
  obtain ⟨k, hclaim⟩ := CfgTPS.Qc_claimed v p (s.req v p eps) k0 S
  obtain ⟨S', S₀', q, hS'S, hS₀S₀', hfoot, hdisj', hq0, hqle, hclaim', hkeep, hsafe, hcosteq⟩ :=
    ChargeTPS.package_of_claimant v p (s.req v p eps) k0 D hp hdisj hadm k hclaim
  have hreq0 : ∀ m, 0 ≤ s.req v p eps m := fun m => QStage.req_nonneg hn hp heps hs m
  have hD0 : 0 ≤ D := QStage.freeBank_nonneg_of hs
  set A : ℝ := ∑ x ∈ S₀', p x with hAdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun x _ => hp x
  set r : ℝ := max 0 (A - q) with hrdef
  have hr0 : 0 ≤ r := le_max_left _ _
  have hqr : q + r = max q A := by
    rcases le_or_gt A q with h | h
    · rw [hrdef, max_eq_left (by linarith : A - q ≤ 0), max_eq_left h, add_zero]
    · rw [hrdef, max_eq_right (by linarith : (0:ℝ) ≤ A - q), max_eq_right h.le]; ring
  have hS'P : S' ⊆ s.pool :=
    Finset.Subset.trans (Finset.Subset.trans hS'S Finset.subset_union_left) hUP
  have hS₀'P : S₀' ⊆ s.pool := fun x hx => hUP (hfoot ▸ Finset.mem_union_right S' hx)
  refine qstep_assign v p eps hn hp heps hs (S := S') (S₀ := S₀') (Src := ∅) (Snew := ∅)
    hS'P hS₀'P hdisj' hq0 hr0 (by simp) (by simp) (Or.inl rfl) (by simp) (by simp) (by simp)
    ?_ ?_ hclaim' hkeep (fun j _ => hsafe j) ?_
  · -- the package is affordable out of the free bank
    intro _
    rw [hqr, ← hAdef]
    rcases le_or_gt A q with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h.le]; linarith
  · -- the sales are self-financed
    rw [hqr, ← hAdef]
    exact le_max_right _ _
  · -- the cost bound
    intro _ j hj
    have hjs : j ∉ s.served := fun h => hj (Finset.mem_insert_of_mem h)
    have hreqj : s.req v p eps j = GeneralTPS.thr v p j := QStage.req_eq_thr hjs
    have hthrj : 0 ≤ GeneralTPS.thr v p j := GeneralTPS.thr_nonneg v p hn hp j
    rcases le_or_gt A q with hAq | hAq
    · have hr0' : r = 0 := by rw [hrdef, max_eq_left (by linarith : A - q ≤ 0)]
      have hcost := CfgTPS.cost_bound (w := v) (p := p) (req := s.req v p eps) (k0 := k0)
        (D := D) (P := s.pool) (S := S) (S₀ := S₀)
        (fun i => TPS n (v i) p) j hp hD0 hreq0
        (by rw [hreqj]; exact ChargeTPS.thr_le_TPS v p hn hp j)
        (by rw [hreqj]; exact ChargeTPS.TPS_le_two_thr v p hn hp j)
        hUP hdisj hadm hmin
      rw [hreqj] at hcost
      have heq := hcosteq (TPS n (v j) p) (v j)
      rw [hr0']
      linarith
    · have hr0' : r = A - q := by rw [hrdef, max_eq_right (by linarith : (0:ℝ) ≤ A - q)]
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
          (fun i => TPS n (v i) p) j hp hD0 hUP hmin hcard
        rw [hreqj] at h2
        linarith
      · have hS₀ne : S₀'.Nonempty := by
          rcases Finset.eq_empty_or_nonempty S₀' with he | he
          · exfalso
            rw [he] at hAdef
            simp only [Finset.sum_empty] at hAdef
            rw [hAdef] at hAq; linarith
          · exact he
        obtain ⟨x, hx⟩ := hS₀ne
        have hxU : x ∈ S ∪ S₀ := hfoot ▸ Finset.mem_union_right S' hx
        have hcard1 : (S ∪ S₀).card = 1 := by
          have : 1 ≤ (S ∪ S₀).card := Finset.card_pos.mpr ⟨x, hxU⟩
          omega
        obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcard1
        have hxy : x = y := by rw [hy] at hxU; simpa using hxU
        subst hxy
        have hxP : x ∈ s.pool := hS₀'P hx
        have hpx : p x ≤ 2 * GeneralTPS.thr v p j := hcheap x hxP j hjs
        have htx : TPS n (v j) p ≤ 2 * GeneralTPS.thr v p j :=
          ChargeTPS.TPS_le_two_thr v p hn hp j
        have h1 : trunc (v j) p (TPS n (v j) p) x ≤ max (p x) (TPS n (v j) p) :=
          trunc_le_max _ _ _ _
        rw [hy]
        simp only [truncBundle, Finset.sum_singleton]
        rcases max_cases (p x) (TPS n (v j) p) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at h1 <;>
          linarith
end FairSelling.PotTPS
