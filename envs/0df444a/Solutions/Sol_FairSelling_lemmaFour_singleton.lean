-- Prove2me | solution 1 for FairSelling.lemmaFour_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:06:46.699314+00:00
-- url     : https://prove2.me/submissions/47a6d867-ce90-403f-a695-0a5f9794e31b

import Mathlib
import Definitions.Def_RequestProject_ConfigSplit
import Definitions.Def_RequestProject_CanonicalStrict
import Definitions.Def_RequestProject_LemmaFourResidual
import Theorems.Thm_FairSelling_config_vbarSum_univ
import Theorems.Thm_FairSelling_vbarSum_insert_disjoint
import Theorems.Thm_FairSelling_MMS2_cash_of_config_split
import Theorems.Thm_FairSelling_MMS2_cash_of_total
import Theorems.Thm_FairSelling_MMS_nonneg
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_config_loss_le
import Theorems.Thm_FairSelling_config_part_sdiff_ge
import Theorems.Thm_FairSelling_config_sold_sdiff
import Theorems.Thm_FairSelling_config_two_parts_sdiff_ge
import Theorems.Thm_FairSelling_exists_part_disjoint
import Theorems.Thm_FairSelling_exists_reduced_three
import Theorems.Thm_FairSelling_fin3_cover
import Theorems.Thm_FairSelling_fin3_others
import Theorems.Thm_FairSelling_fin3_sum
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_vbarSum_sdiff
import Theorems.Thm_P2M_FairSelling_vbarSum_nonneg__de2d262c4ecf
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
    (hnobig : ∀ g, vbar w p g < (3 / 4 : ℝ) * MMS 3 w p)
    (K : Finset G) (f : G) (m : ℝ) (hfK : f ∉ K) (hm0 : 0 ≤ m) (hmf : m ≤ p f)
    (hKcard : K.card ≤ 1) (hprice : (1 / 4 : ℝ) * MMS 3 w p ≤ p f)
    (hrej : vbarSum w p K + m ≤ (3 / 4 : ℝ) * MMS 3 w p) :
    (3 / 4 : ℝ) * MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ (K ∪ {f})) w)
      (cashPrice (Finset.univ \ (K ∪ {f})) p (p f - m)) := by
  classical
  set M : ℝ := MMS 3 w p with hM
  set τ : ℝ := (3 / 4 : ℝ) * M with hτ
  have hM0 : 0 ≤ M := MMS_nonneg (by norm_num) w p hw hp
  set X : Finset G := K ∪ {f} with hX
  have hXcard : X.card ≤ 2 := by
    have h := Finset.card_union_le K ({f} : Finset G)
    simp only [Finset.card_singleton] at h
    rw [hX]
    omega
  have hvX : vbarSum w p X = vbarSum w p K + vbar w p f := vbarSum_insert_disjoint w p K f hfK
  have hvK0 : 0 ≤ vbarSum w p K := vbarSum_nonneg' w p hw K
  have hfbig : vbar w p f < τ := hnobig f
  have hpf_le : p f ≤ vbar w p f := le_max_left _ _
  obtain ⟨A, s, q, hcfg, hscard⟩ := exists_reduced_three w p hw hp
  have hq0 := hcfg.2.2.2.1
  have hqsum := hcfg.2.2.2.2.1
  have hge := hcfg.2.2.2.2.2
  by_cases hfs : f ∈ s
  · -- The agent sells `f` itself: the forced sale destroys no value, and counting suffices.
    have hslack : vbar w p f - p f ≤ vbarSum w p s - ∑ g ∈ s, p g := by
      have hterm : ∀ g ∈ s, (0 : ℝ) ≤ vbar w p g - p g := fun g _ => by
        simp only [vbar, sub_nonneg]; exact le_max_left _ _
      have hsum : ∑ g ∈ s, (vbar w p g - p g) = vbarSum w p s - ∑ g ∈ s, p g := by
        rw [Finset.sum_sub_distrib]; rfl
      have hone : vbar w p f - p f ≤ ∑ g ∈ s, (vbar w p g - p g) :=
        Finset.single_le_sum (f := fun g => vbar w p g - p g) hterm hfs
      linarith
    have hV : vbarSum w p Finset.univ = (∑ i, vbarSum w p (A i)) + vbarSum w p s :=
      config_vbarSum_univ w p hcfg
    have hparts : 3 * M - ∑ i, q i ≤ ∑ i, vbarSum w p (A i) := by
      have h := Finset.sum_le_sum (fun (i : Fin 3) (_ : i ∈ Finset.univ) => hge i)
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] at h
      push_cast at h
      linarith
    have hRem : vbarSum w p (Finset.univ \ X)
        = vbarSum w p Finset.univ - vbarSum w p X := vbarSum_sdiff w p (Finset.subset_univ X)
    refine MMS2_cash_of_total w p hw hp (Finset.univ \ X) (p f - m) τ (by linarith) (by linarith)
      (fun g _ => (hnobig g).le) ?_
    rw [hRem, hvX]
    linarith
  · -- `f` is kept in one part of the configuration.
    obtain ⟨i0, hi0⟩ : ∃ i0 : Fin 3, f ∈ A i0 := by
      have hf' : f ∈ s ∪ Finset.univ.biUnion A := by
        rw [hcfg.2.2.1]; exact Finset.mem_univ f
      rcases Finset.mem_union.mp hf' with h | h
      · exact absurd h hfs
      · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp h
        exact ⟨i, hi⟩
    have hsX : s ∩ X ⊆ K := by
      intro x hx
      obtain ⟨hxs, hxX⟩ := Finset.mem_inter.mp hx
      rcases Finset.mem_union.mp hxX with h | h
      · exact h
      · exact absurd (Finset.mem_singleton.mp h ▸ hxs) hfs
    -- the untouched parts, and among them one with least proceeds share
    set U : Finset (Fin 3) := Finset.univ.filter (fun k => Disjoint (A k) X) with hU
    have hUne : U.Nonempty := by
      obtain ⟨j, hj⟩ := exists_part_disjoint A hcfg.1 X hXcard
      exact ⟨j, by simp [hU, hj]⟩
    obtain ⟨j, hjU, hjmin⟩ := Finset.exists_min_image (f := q) U hUne
    have hjdisj : Disjoint (A j) X := by simpa [hU] using hjU
    obtain ⟨j', j'', hj', hj'', hj'j''⟩ := fin3_others j
    have hj1 : j ≠ j' := Ne.symm hj'
    have hj2 : j ≠ j'' := Ne.symm hj''
    -- abbreviations for the pieces of the split
    set LC : ℝ := vbarSum w p (A j ∩ X) with hLC
    set LD : ℝ := vbarSum w p ((A j' ∪ A j'') ∩ X) with hLD
    set PS : ℝ := ∑ g ∈ s ∩ X, p g with hPS
    have hLC0 : LC = 0 := by
      have : A j ∩ X = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hjdisj
      simp [hLC, this, vbarSum]
    have hLD0 : 0 ≤ LD := vbarSum_nonneg' w p hw _
    have hPS0 : 0 ≤ PS := Finset.sum_nonneg (fun g _ => hp g)
    have hPSK : PS ≤ vbarSum w p K := by
      refine le_trans (Finset.sum_le_sum (fun g _ => le_max_left (p g) (w g))) ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg hsX
        (fun g _ _ => le_trans (hw g) (le_max_right _ _))
    have hPSq : PS ≤ ∑ i, q i := by
      rw [hqsum]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun g _ _ => hp g)
    have hloss : LC + LD + PS ≤ vbarSum w p X := config_loss_le w p hcfg X hj1 hj2 hj'j''
    have hC := config_part_sdiff_ge w p hcfg X j
    have hD := config_two_parts_sdiff_ge w p hcfg X hj'j''
    have hT := config_sold_sdiff w p hcfg X
    -- either the lost proceeds are covered by the banked cash, or a second part is untouched
    have hcase : PS ≤ p f - m ∨ ∃ k, k ≠ j ∧ Disjoint (A k) X ∧ q j ≤ q k := by
      by_cases hle : PS ≤ p f - m
      · exact Or.inl hle
      · refine Or.inr ?_
        push_neg at hle
        have hne : (s ∩ X).Nonempty := by
          rcases Finset.eq_empty_or_nonempty (s ∩ X) with h | h
          · exfalso; rw [hPS, h] at hle; simp at hle; linarith
          · exact h
        obtain ⟨e, he⟩ := hne
        have heK : e ∈ K := hsX he
        have hKeq : K = {e} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨heK, fun x hx => Finset.card_le_one.mp hKcard x hx e heK⟩
        have hes : e ∈ s := (Finset.mem_inter.mp he).1
        -- only the part containing `f` is touched
        have huntouched : ∀ k, k ≠ i0 → Disjoint (A k) X := by
          intro k hk
          refine Finset.disjoint_left.mpr (fun x hx hxX => ?_)
          rcases Finset.mem_union.mp hxX with h | h
          · rw [hKeq, Finset.mem_singleton] at h
            exact (Finset.disjoint_left.mp (hcfg.2.1 k)) (h ▸ hes) hx
          · rw [Finset.mem_singleton] at h
            exact hk (by
              by_contra hne
              exact (Finset.disjoint_left.mp (hcfg.1 k i0 hne)) hx (h ▸ hi0))
        obtain ⟨k1, k2, hk1, hk2, hk12⟩ := fin3_others i0
        rcases eq_or_ne k1 j with rfl | hne1
        · exact ⟨k2, Ne.symm hk12, huntouched k2 hk2,
            hjmin k2 (by simp [hU, huntouched k2 hk2])⟩
        · exact ⟨k1, hne1, huntouched k1 hk1, hjmin k1 (by simp [hU, huntouched k1 hk1])⟩
    rw [hvX] at hloss
    have hqj := hq0 j
    have hqj' := hq0 j'
    have hqj'' := hq0 j''
    have hsum3 : ∑ i, q i = q j + q j' + q j'' := fin3_sum hj1 hj2 hj'j'' q
    -- the crucial estimate: if the isolated part needs money, the other two parts hold enough
    have hkey : M / 4 < q j → τ - M + m - p f + PS ≤ q j' + q j'' := by
      intro hqbig
      rcases hcase with hcov | ⟨k, hkj, -, hqk⟩
      · linarith
      · have hqpair : q j ≤ q j' + q j'' := by
          rcases fin3_cover hj1 hj2 hj'j'' k with h | h | h
          · exact absurd h hkj
          · rw [h] at hqk; linarith
          · rw [h] at hqk; linarith
        linarith
    refine MMS2_cash_of_config_split w p hw hp hcfg X (p f - m) τ (by linarith) hj1 hj2 ?_
    rw [hT, ← hPS]
    rcases le_or_gt τ (vbarSum w p (A j \ X)) with h1 | h1 <;>
      rcases le_or_gt τ (vbarSum w p ((A j' ∪ A j'') \ X)) with h2 | h2
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; linarith
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      have := hkey (by linarith)
      linarith
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; linarith
end FairSelling
