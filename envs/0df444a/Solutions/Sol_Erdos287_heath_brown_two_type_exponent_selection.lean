-- Prove2me | solution 1 for Erdos287.heath_brown_two_type_exponent_selection
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T15:29:02.330214+00:00
-- url     : https://prove2.me/submissions/1fc84f6f-488e-4a1f-b9a3-36910d492148

import Mathlib

set_option autoImplicit false

private theorem partial_sum_of_small_weights {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ I, 0 ≤ x i ∧ x i < 1 / 10)
    (h : 1 / 10 ≤ ∑ i ∈ I, x i) :
    ∃ J ⊆ I, 1 / 10 ≤ ∑ i ∈ J, x i ∧ ∑ i ∈ J, x i ≤ 1 / 5 := by
  induction I using Finset.induction_on with
  | empty => simp only [Finset.sum_empty] at h; norm_num at h
  | @insert i I hi ih =>
      have hxs j (hj : j ∈ I) := hx j (Finset.mem_insert_of_mem hj)
      by_cases hI : 1 / 10 ≤ ∑ j ∈ I, x j
      · obtain ⟨J, hJ, hJlo, hJhi⟩ := ih hxs hI
        exact ⟨J, hJ.trans (Finset.subset_insert _ _), hJlo, hJhi⟩
      · have hlast := (hx i (Finset.mem_insert_self _ _)).2
        refine ⟨insert i I, Finset.Subset.rfl, h, ?_⟩
        rw [Finset.sum_insert hi]
        linarith

/-- The exponent boxes in the four-fold Heath–Brown decomposition either
contain a large smooth variable or a partial product of Type II size. -/
theorem solution {ι : Type*} [DecidableEq ι] (I smooth : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ I, 0 ≤ x i) (hsum : ∑ i ∈ I, x i = 1)
    (hrough : ∀ i ∈ I, i ∉ smooth → x i ≤ 251 / 1000) :
    (∃ i ∈ I, i ∈ smooth ∧ 3 / 10 ≤ x i) ∨
    ∃ J ⊆ I, 1 / 10 ≤ ∑ i ∈ J, x i ∧ ∑ i ∈ J, x i ≤ 251 / 1000 := by
  classical
  by_cases hs : ∃ i ∈ I, i ∈ smooth ∧ 3 / 10 ≤ x i
  · exact Or.inl hs
  right
  by_cases hm : ∃ i ∈ I, 1 / 10 ≤ x i ∧ x i ≤ 251 / 1000
  · obtain ⟨i, hi, hlo, hhi⟩ := hm
    exact ⟨{i}, Finset.singleton_subset_iff.mpr hi,
      by simpa only [Finset.sum_singleton] using hlo,
      by simpa only [Finset.sum_singleton] using hhi⟩
  let small := I.filter (fun i => x i < 1 / 10)
  let big := I.filter (fun i => 251 / 1000 < x i)
  have hdisjoint : Disjoint small big := by
    apply Finset.disjoint_left.mpr
    intro i hs' hb'
    have hsmall := (Finset.mem_filter.mp hs').2
    have hbig := (Finset.mem_filter.mp hb').2
    linarith
  have hunion : small ∪ big = I := by
    ext i
    simp only [Finset.mem_union, small, big, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hi
      by_cases h : x i < 1 / 10
      · exact Or.inl ⟨hi, h⟩
      · exact Or.inr ⟨hi, lt_of_not_ge fun h' => hm ⟨i, hi, le_of_not_gt h, h'⟩⟩
  have hsplit : (∑ i ∈ small, x i) + (∑ i ∈ big, x i) = 1 := by
    rw [← Finset.sum_union hdisjoint, hunion, hsum]
  have hbcard : big.card ≤ 3 := by
    by_contra! hcard
    have hnonempty : big.Nonempty := Finset.card_pos.mp (by omega)
    have hquad : (big.card : ℝ) * (1 / 4) < ∑ i ∈ big, x i := by
      have hsumlt := Finset.sum_lt_sum_of_nonempty (f := fun _ => (1 / 4 : ℝ))
        (g := x) hnonempty (fun i hi => lt_trans (by norm_num) (Finset.mem_filter.mp hi).2)
      simpa [nsmul_eq_mul] using hsumlt
    have hfour : (4 : ℝ) ≤ (big.card : ℝ) := by exact_mod_cast hcard
    have hnonneg : 0 ≤ ∑ i ∈ small, x i :=
      Finset.sum_nonneg fun i hi => hx i (Finset.mem_filter.mp hi).1
    linarith
  have hbig : (∑ i ∈ big, x i) ≤ 9 / 10 := calc
    _ ≤ ∑ _i ∈ big, (3 / 10 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hiI, hgt⟩ := Finset.mem_filter.mp hi
      have his : i ∈ smooth := by by_contra h; have := hrough i hiI h; linarith
      exact le_of_lt (lt_of_not_ge fun h => hs ⟨i, hiI, his, h⟩)
    _ ≤ _ := by
      have hc : (big.card : ℝ) ≤ 3 := by exact_mod_cast hbcard
      simp [nsmul_eq_mul]
      linarith
  have hsmall : 1 / 10 ≤ ∑ i ∈ small, x i := by linarith
  obtain ⟨J, hJ, hlo, hhi⟩ := partial_sum_of_small_weights small x
    (fun i hi => ⟨hx i (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩) hsmall
  exact ⟨J, hJ.trans (Finset.filter_subset _ _), hlo, hhi.trans (by norm_num)⟩

