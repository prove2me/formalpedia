-- Prove2me | solution 1 for FairSelling.ChargeTPS.package_of_claimant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:59:26.970981+00:00
-- url     : https://prove2.me/submissions/60ee3b1a-1c8f-4fca-b5dd-ab34feda024a

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Theorems.Thm_FairSelling_CfgTPS_Qc_nonneg
import Theorems.Thm_FairSelling_CfgTPS_Qc_safe
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_ChargeTPS_sum_saleLoss
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_truncBundle_sdiff
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (req : Fin n → ℝ) (k0 : Fin n) (D : ℝ)
omit [Fintype G]
namespace FairSelling.ChargeTPS
theorem _root_.solution (hp : ∀ g, 0 ≤ p g) {S S₀ : Finset G} (hdisj : Disjoint S S₀)
    (hadm : CfgTPS.Adm v p req k0 D S S₀) (k : Fin n)
    (hclaim : req k ≤ vbarSum (v k) p S + CfgTPS.Qc v p req k0 S) :
    ∃ (S' S₀' : Finset G) (q : ℝ),
      S' ⊆ S ∧ S₀ ⊆ S₀' ∧ S' ∪ S₀' = S ∪ S₀ ∧ Disjoint S' S₀' ∧
      0 ≤ q ∧ q ≤ D + ∑ g ∈ S₀', p g ∧
      req k ≤ vbarSum (v k) p S' + q ∧ (∀ g ∈ S', p g ≤ v k g) ∧
      (∀ m, (vbarSum (v m) p S' + q ≤ req m) ∨
        (q = 0 ∧ ∀ g ∈ S', vbarSum (v m) p (S' \ {g}) + p g ≤ req m)) ∧
      (∀ (t : ℝ) (u : G → ℝ),
        truncBundle u p t S' + q + ∑ g ∈ S₀', saleLoss u p t g
          = truncBundle u p t S + CfgTPS.Qc v p req k0 S + ∑ g ∈ S₀, saleLoss u p t g) := by
  classical
  set Q := CfgTPS.Qc v p req k0 S with hQ
  set X : Finset G := S.filter (fun g => v k g < p g) with hX
  have hXS : X ⊆ S := Finset.filter_subset _ _
  have hXS₀ : Disjoint X S₀ := Finset.disjoint_of_subset_left hXS hdisj
  have hpX : 0 ≤ ∑ g ∈ X, p g := Finset.sum_nonneg (fun g _ => hp g)
  have hQ0 : 0 ≤ Q := CfgTPS.Qc_nonneg v p req k0 S
  refine ⟨S \ X, S₀ ∪ X, Q + ∑ g ∈ X, p g, Finset.sdiff_subset, Finset.subset_union_left, ?_, ?_,
    by linarith, ?_, ?_, ?_, ?_, ?_⟩
  · -- same footprint
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    by_cases hx : x ∈ X
    · have := hXS hx; tauto
    · tauto
  · -- disjointness
    refine Finset.disjoint_union_right.mpr ⟨?_, ?_⟩
    · exact Finset.disjoint_of_subset_left Finset.sdiff_subset hdisj
    · exact Finset.sdiff_disjoint
  · -- affordable
    have hsum : ∑ g ∈ S₀ ∪ X, p g = (∑ g ∈ S₀, p g) + ∑ g ∈ X, p g :=
      Finset.sum_union hXS₀.symm
    have := hadm.1
    unfold CfgTPS.Feas at this
    rw [hsum]
    rw [← hQ] at this
    linarith
  · -- the claimant still claims
    have hsplit : vbarSum (v k) p S = vbarSum (v k) p (S \ X) + ∑ g ∈ X, vbar (v k) p g := by
      unfold vbarSum
      exact (Finset.sum_sdiff hXS).symm
    have hXp : ∑ g ∈ X, vbar (v k) p g = ∑ g ∈ X, p g := by
      refine Finset.sum_congr rfl (fun g hg => ?_)
      have : v k g < p g := (Finset.mem_filter.mp hg).2
      exact max_eq_left (le_of_lt this)
    rw [hXp] at hsplit
    linarith
  · -- the claimant keeps the goods
    intro g hg
    have hgS : g ∈ S := (Finset.mem_sdiff.mp hg).1
    have hgX : g ∉ X := (Finset.mem_sdiff.mp hg).2
    have : ¬ (v k g < p g) := by
      intro h
      exact hgX (Finset.mem_filter.mpr ⟨hgS, h⟩)
    linarith [not_lt.mp this]
  · -- safety
    intro m
    rcases Finset.eq_empty_or_nonempty X with hXe | hXne
    · -- nothing was moved
      have hSe : S \ X = S := by rw [hXe]; simp
      have hqe : Q + ∑ g ∈ X, p g = Q := by rw [hXe]; simp
      rcases eq_or_lt_of_le hQ0 with hQz | hQpos
      · right
        refine ⟨by rw [hqe, ← hQz], ?_⟩
        intro g hg
        rw [hSe] at hg ⊢
        have := hadm.2 {g} (Finset.singleton_subset_iff.mpr hg) ⟨g, by simp⟩ m
        simp only [Finset.sum_singleton] at this
        rw [← hQ, ← hQz] at this
        simpa using this
      · left
        rw [hSe, hqe]
        have := CfgTPS.Qc_safe v p req k0 (S := S) (by rw [← hQ]; exact hQpos) m
        rw [← hQ] at this
        exact this
    · left
      have := hadm.2 X hXS hXne m
      rw [← hQ] at this
      linarith
  · -- the cost is unchanged
    intro t u
    have h1 : truncBundle u p t S = truncBundle u p t (S \ X) + truncBundle u p t X :=
      truncBundle_sdiff u p t hXS
    have h2 : ∑ g ∈ S₀ ∪ X, saleLoss u p t g
        = (∑ g ∈ S₀, saleLoss u p t g) + ∑ g ∈ X, saleLoss u p t g :=
      Finset.sum_union hXS₀.symm
    have h3 : ∑ g ∈ X, saleLoss u p t g = truncBundle u p t X - ∑ g ∈ X, p g :=
      sum_saleLoss u p t X
    rw [h2, h3]
    linarith
end FairSelling.ChargeTPS
