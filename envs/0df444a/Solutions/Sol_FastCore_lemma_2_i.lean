-- Prove2me | solution 1 for FastCore.lemma_2_i
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:54:40.670168+00:00
-- url     : https://prove2.me/submissions/4279d4e6-6a36-46c0-8b01-0d436d61eddd

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_trunc
import Definitions.Def_FastCore_IsZeroFreeWinnerSet
import Definitions.Def_FastCore_IsMBCC

namespace Aux_FastCore_l2i
open FastCore ComplementFreeCA.CFRounding

open scoped Classical in
theorem w_spec {n m : ℕ} (b : Bids n m) (T : Finset (Fin n)) :
    ∃ y, (IsAllocation y ∧ ∀ i, i ∉ T → y i = ∅) ∧ w b T = welfare b y := by
  unfold w
  obtain ⟨y, hy, he⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.univ.filter (fun x : Fin n → Finset (Fin m) =>
      IsAllocation x ∧ ∀ i, i ∉ T → x i = ∅))
    ⟨fun _ => ∅, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun _ _ _ => Finset.disjoint_empty_left _, fun _ _ => rfl⟩⟩ (welfare b)
  exact ⟨y, (Finset.mem_filter.mp hy).2, he⟩

open scoped Classical in
theorem w_ge {n m : ℕ} (b : Bids n m) (T : Finset (Fin n)) (y : Fin n → Finset (Fin m))
    (hy : IsAllocation y) (hT : ∀ i, i ∉ T → y i = ∅) : welfare b y ≤ w b T := by
  unfold w
  exact Finset.le_sup' (welfare b) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy, hT⟩)

theorem welfare_supp {n m : ℕ} (b : Bids n m) (hb : ∀ i, b i ∅ = 0) (T : Finset (Fin n))
    (y : Fin n → Finset (Fin m)) (hT : ∀ i, i ∉ T → y i = ∅) :
    welfare b y = ∑ i ∈ T, b i (y i) := by
  unfold welfare
  symm
  apply Finset.sum_subset (Finset.subset_univ T)
  intro i _ hi
  rw [hT i hi, hb i]

end Aux_FastCore_l2i

open FastCore ComplementFreeCA.CFRounding Aux_FastCore_l2i in
theorem solution {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) {π : Fin n → ℝ}
    (hπ : ∀ i, 0 ≤ π i) {S : Finset (Fin n)} (hS : IsZeroFreeWinnerSet (trunc b π) S) :
    IsMBCC b π S := by
  obtain ⟨x, ⟨hxA, hxmax⟩, hpos, rfl⟩ := hS
  intro S'
  obtain ⟨y, ⟨hyA, hyT⟩, he⟩ := w_spec b S'
  have hxT : ∀ i, i ∉ winners x → x i = ∅ := by
    intro i hi
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have h1 : w b S' - ∑ i ∈ S', π i ≤ ∑ i ∈ S', trunc b π i (y i) := by
    rw [he, welfare_supp b hb.1 S' y hyT, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    exact le_max_left _ _
  have h2 : ∑ i ∈ S', trunc b π i (y i) ≤ welfare (trunc b π) y := by
    unfold welfare
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => le_max_right _ _)
  have h3 := hxmax y hyA
  have h4 : welfare (trunc b π) x = ∑ i ∈ winners x, (b i (x i) - π i) := by
    unfold welfare
    have hz : ∀ i ∈ Finset.univ, i ∉ winners x → trunc b π i (x i) = 0 := by
      intro i _ hi
      rw [hxT i hi]; unfold trunc; rw [hb.1 i]; exact max_eq_right (by linarith [hπ i])
    rw [← Finset.sum_subset (Finset.subset_univ (winners x)) hz]
    apply Finset.sum_congr rfl
    intro i hi
    have hxi : x i ≠ ∅ := (Finset.mem_filter.mp hi).2
    have hp := hpos i hxi
    unfold trunc at hp ⊢
    apply max_eq_left
    by_contra hc2
    push_neg at hc2
    rw [max_eq_right hc2.le] at hp
    exact lt_irrefl _ hp
  have h5 : welfare b x = ∑ i ∈ winners x, b i (x i) := welfare_supp b hb.1 _ x hxT
  have h6 := w_ge b (winners x) x hxA hxT
  rw [h4, Finset.sum_sub_distrib] at h3
  linarith
