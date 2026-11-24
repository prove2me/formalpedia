-- Prove2me | solution 1 for FairSelling.MMS2_cash_of_one_good_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:06:32.97414+00:00
-- url     : https://prove2.me/submissions/093d2440-0469-4cd5-9962-a7faa9629ebc

import Mathlib
import Definitions.Def_RequestProject_LemmaFourResidual
import Definitions.Def_RequestProject_PreliminaryPhase
import Theorems.Thm_FairSelling_MMS2_cash_of_config_split
import Theorems.Thm_FairSelling_MMS_nonneg
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_config_merged_ge_one
import Theorems.Thm_FairSelling_config_part_sdiff_ge
import Theorems.Thm_FairSelling_config_sold_sdiff
import Theorems.Thm_FairSelling_config_two_parts_sdiff_ge
import Theorems.Thm_FairSelling_exists_reduced_three
import Theorems.Thm_FairSelling_fin3_cover
import Theorems.Thm_FairSelling_fin3_others
import Theorems.Thm_FairSelling_fin3_sum
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some
attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.mem_optionGoods
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (e : G) (c m : ℝ) (hc : 0 ≤ c) (hm0 : 0 ≤ m)
    (hmτ : m ≤ (3 / 4 : ℝ) * MMS 3 w p) (hme : m ≤ p e) (hcm : p e ≤ c + m) :
    (3 / 4 : ℝ) * MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ {e}) w)
      (cashPrice (Finset.univ \ {e}) p c) := by
  classical
  set M : ℝ := MMS 3 w p with hM
  set τ : ℝ := (3 / 4 : ℝ) * M with hτ
  have hM0 : 0 ≤ M := MMS_nonneg (by norm_num) w p hw hp
  set X : Finset G := {e} with hX
  obtain ⟨A, s, q, hcfg, -⟩ := exists_reduced_three w p hw hp
  have hq0 := hcfg.2.2.2.1
  have hqsum := hcfg.2.2.2.2.1
  have hT := config_sold_sdiff w p hcfg X
  by_cases hes : e ∈ s
  · -- The agent sells `e` itself: every part survives, only some proceeds are lost.
    have hXparts : ∀ k : Fin 3, A k ∩ X = ∅ := by
      intro k
      refine Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => ?_)
      obtain ⟨hxk, hxX⟩ := Finset.mem_inter.mp hx
      rw [hX, Finset.mem_singleton] at hxX
      exact (Finset.disjoint_left.mp (hcfg.2.1 k)) (hxX ▸ hes) hxk
    obtain ⟨j, -, hjmin⟩ :=
      Finset.exists_min_image (f := q) (Finset.univ : Finset (Fin 3)) ⟨0, Finset.mem_univ 0⟩
    obtain ⟨j', j'', hj', hj'', hj'j''⟩ := fin3_others j
    have hj1 : j ≠ j' := Ne.symm hj'
    have hj2 : j ≠ j'' := Ne.symm hj''
    have hPS : ∑ g ∈ s ∩ X, p g = p e := by
      have : s ∩ X = {e} := by
        rw [hX]
        ext x
        simp only [Finset.mem_inter, Finset.mem_singleton]
        constructor
        · rintro ⟨-, hx⟩; exact hx
        · rintro rfl; exact ⟨hes, rfl⟩
      rw [this, Finset.sum_singleton]
    have hPSq : p e ≤ ∑ i, q i := by
      rw [hqsum]
      exact Finset.single_le_sum (f := p) (fun g _ => hp g) hes
    have hC := config_part_sdiff_ge w p hcfg X j
    have hD := config_two_parts_sdiff_ge w p hcfg X hj'j''
    have hLC : vbarSum w p (A j ∩ X) = 0 := by simp [hXparts j, vbarSum]
    have hLD : vbarSum w p ((A j' ∪ A j'') ∩ X) = 0 := by
      have : (A j' ∪ A j'') ∩ X = ∅ := by
        rw [Finset.union_inter_distrib_right, hXparts j', hXparts j'']
        simp
      simp [this, vbarSum]
    have hqj := hq0 j
    have hqj' := hq0 j'
    have hqj'' := hq0 j''
    have hmin' : q j ≤ q j' := hjmin j' (Finset.mem_univ j')
    have hmin'' : q j ≤ q j'' := hjmin j'' (Finset.mem_univ j'')
    have hsum3 : ∑ i, q i = q j + q j' + q j'' := fin3_sum hj1 hj2 hj'j'' q
    refine MMS2_cash_of_config_split w p hw hp hcfg X c τ hc hj1 hj2 ?_
    rw [hT, hPS]
    rcases le_or_gt τ (vbarSum w p (A j \ X)) with h1 | h1 <;>
      rcases le_or_gt τ (vbarSum w p ((A j' ∪ A j'') \ X)) with h2 | h2
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; linarith
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; linarith
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; linarith
  · -- The agent keeps `e` in one of its parts: the other two parts survive untouched.
    obtain ⟨i0, hi0⟩ : ∃ i0 : Fin 3, e ∈ A i0 := by
      have he' : e ∈ s ∪ Finset.univ.biUnion A := by
        rw [hcfg.2.2.1]; exact Finset.mem_univ e
      rcases Finset.mem_union.mp he' with h | h
      · exact absurd h hes
      · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp h
        exact ⟨i, hi⟩
    have huntouched : ∀ k : Fin 3, k ≠ i0 → A k ∩ X = ∅ := by
      intro k hk
      refine Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => ?_)
      obtain ⟨hxk, hxX⟩ := Finset.mem_inter.mp hx
      rw [hX, Finset.mem_singleton] at hxX
      exact (Finset.disjoint_left.mp (hcfg.1 k i0 hk)) hxk (hxX ▸ hi0)
    obtain ⟨k1, k2, hk1, hk2, hk12⟩ := fin3_others i0
    obtain ⟨j', j'', hj', hj'', hj'j''⟩ := fin3_others k1
    have hj1 : k1 ≠ j' := Ne.symm hj'
    have hj2 : k1 ≠ j'' := Ne.symm hj''
    have hk2mem : k2 = j' ∨ k2 = j'' := by
      rcases fin3_cover hj1 hj2 hj'j'' k2 with h | h | h
      · exact absurd h (Ne.symm hk12)
      · exact Or.inl h
      · exact Or.inr h
    have hC := config_part_sdiff_ge w p hcfg X k1
    have hD := config_merged_ge_one w p hw hcfg X (j' := j') (j'' := j'') hk2mem
    have hLC : vbarSum w p (A k1 ∩ X) = 0 := by simp [huntouched k1 hk1, vbarSum]
    have hLD : vbarSum w p (A k2 ∩ X) = 0 := by simp [huntouched k2 hk2, vbarSum]
    have hPS : ∑ g ∈ s ∩ X, p g = 0 := by
      have : s ∩ X = ∅ := by
        rw [hX]
        refine Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => ?_)
        obtain ⟨hxs, hxX⟩ := Finset.mem_inter.mp hx
        rw [Finset.mem_singleton] at hxX
        exact hes (hxX ▸ hxs)
      rw [this, Finset.sum_empty]
    have hqk1 := hq0 k1
    have hqk2 := hq0 k2
    have hqsum3 : q k1 + q k2 ≤ ∑ i, q i := by
      have hsum3 : ∑ i, q i = q i0 + q k1 + q k2 :=
        fin3_sum (Ne.symm hk1) (Ne.symm hk2) hk12 q
      have := hq0 i0
      linarith
    refine MMS2_cash_of_config_split w p hw hp hcfg X c τ hc hj1 hj2 ?_
    rw [hT, hPS]
    rcases le_or_gt τ (vbarSum w p (A k1 \ X)) with h1 | h1 <;>
      rcases le_or_gt τ (vbarSum w p ((A j' ∪ A j'') \ X)) with h2 | h2
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; linarith
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; linarith
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; linarith
end FairSelling
