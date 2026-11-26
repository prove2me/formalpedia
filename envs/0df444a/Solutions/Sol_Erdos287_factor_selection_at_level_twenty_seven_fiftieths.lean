-- Prove2me | solution 1 for Erdos287.factor_selection_at_level_twenty_seven_fiftieths
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T20:36:33.1644+00:00
-- url     : https://prove2.me/submissions/36332512-2c1c-428c-8d2a-ba1c799ed343

import Mathlib

set_option autoImplicit false

private theorem select_small {ι : Type*} [DecidableEq ι]
    (x : ι → ℝ) (S : Finset ι) (hsmall : ∀ i ∈ S, x i < 801 / 10000)
    (hsum : 801 / 10000 ≤ ∑ i ∈ S, x i) :
    ∃ J ⊆ S, 801 / 10000 ≤ ∑ i ∈ J, x i ∧ ∑ i ∈ J, x i ≤ 613 / 2000 := by
  induction S using Finset.induction_on with
  | empty => norm_num at hsum
  | @insert i S hi ih =>
    by_cases htail : 801 / 10000 ≤ ∑ j ∈ S, x j
    · obtain ⟨J, hJ, hlo, hhi⟩ :=
        ih (fun j hj => hsmall j (Finset.mem_insert_of_mem hj)) htail
      exact ⟨J, hJ.trans (Finset.subset_insert i S), hlo, hhi⟩
    · refine ⟨insert i S, Finset.Subset.refl _, hsum, ?_⟩
      rw [Finset.sum_insert hi]
      linarith [hsmall i (Finset.mem_insert_self i S)]

/-- The Type I, Type II and Type III scale tests at level 27/50 leave only
a narrow band of boxes with precisely three large smooth constituents. -/
theorem solution {ι : Type*} [DecidableEq ι] (I smooth : Finset ι) (x : ι → ℝ)
    (hpos : ∀ i ∈ I, 0 ≤ x i) (hsum : ∑ i ∈ I, x i = 1)
    (hrough : ∀ i ∈ I, i ∉ smooth → x i ≤ 251 / 1000)
    (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ 1 / 1000000) :
    ((∃ i ∈ I, i ∈ smooth ∧ 3101 / 10000 ≤ x i) ∨
      (∃ J ⊆ I, 801 / 10000 ≤ ∑ i ∈ J, x i ∧ ∑ i ∈ J, x i ≤ 613 / 2000) ∨
      ∃ L ⊆ I, L.card = 3 ∧
        (∀ i ∈ L, i ∈ smooth ∧ 613 / 2000 < x i ∧ x i < 3101 / 10000) ∧
        (697 / 10000 ≤ ∑ i ∈ I \ L, x i) ∧
        ((∑ i ∈ I \ L, x i) ≤ 183 / 2500 ∨
          183 / 2500 < (∑ i ∈ I \ L, x i) ∧ (∑ i ∈ I \ L, x i) < 801 / 10000)) ∧
    (∀ m r s : ℝ, 3101 / 10000 ≤ m → m ≤ 1 → 0 ≤ r → 0 ≤ s →
      s ≤ m - ε → r ≤ 27 / 50 - m + 2 * ε →
      (s - m) / 2 ≤ -ε / 2 ∧ r + s / 2 + 1 / 2 ≤ 1 - ε ∧
      r + s / 4 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      3 * r / 4 + s / 2 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      r / 2 + s / 4 - 3 * m / 4 ≤ -ε) ∧
    (∀ ν r s : ℝ, 801 / 10000 ≤ ν → ν ≤ 613 / 2000 → 0 ≤ r → 0 ≤ s →
      r ≤ 27 / 50 - ν + 2 * ε → s ≤ ν - ε →
      2 * r + ν ≤ 1 - ε ∧ r / 2 + 5 * ν / 4 ≤ 1 / 2 - ε ∧
      3 * r / 4 + ν ≤ 1 / 2 - ε ∧ r + 3 * ν / 2 ≤ 1 - ε ∧
      (r - s / 2 + ν ≤ 1 / 2 - ε ∨
        r + s / 2 ≤ 1 / 2 - ε ∧ 7 * r / 4 + 5 * ν / 4 + s ≤ 1 - ε)) ∧
    (∀ a q r s : ℝ, a ≤ 183 / 2500 → 0 ≤ q → q ≤ ε →
      0 ≤ r → r ≤ 23 / 75 + ε → 0 ≤ s → s ≤ 7 / 30 + ε →
      a + 4 * q + 4 * r + 3 * s - 1 ≤ 1 - ε ∧
      a + 7 * q / 4 + 7 * r / 4 + 3 * s / 2 ≤ 1 - ε ∧
      a + 3 * q / 2 + 3 * r / 2 + 2 * s ≤ 1 - ε) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hI : ∃ i ∈ I, i ∈ smooth ∧ 3101 / 10000 ≤ x i
    · exact Or.inl hI
    right
    let L := I.filter fun i => 801 / 10000 ≤ x i
    have hLI : L ⊆ I := Finset.filter_subset _ _
    by_cases hsingle : ∃ i ∈ L, x i ≤ 613 / 2000
    · obtain ⟨i, hi, hhi⟩ := hsingle
      have hlo := (Finset.mem_filter.mp hi).2
      exact Or.inl ⟨{i}, Finset.singleton_subset_iff.mpr (hLI hi),
        by simpa using hlo, by simpa using hhi⟩
    have hshort (i : ι) (hi : i ∈ I \ L) : x i < 801 / 10000 := by
      obtain ⟨hiI, hiL⟩ := Finset.mem_sdiff.mp hi
      exact lt_of_not_ge fun h => hiL (Finset.mem_filter.mpr ⟨hiI, h⟩)
    by_cases hsmall : 801 / 10000 ≤ ∑ i ∈ I \ L, x i
    · obtain ⟨J, hJ, hlo, hhi⟩ := select_small x (I \ L) hshort hsmall
      exact Or.inl ⟨J, hJ.trans Finset.sdiff_subset, hlo, hhi⟩
    right
    have hband (i : ι) (hi : i ∈ L) :
        i ∈ smooth ∧ 613 / 2000 < x i ∧ x i < 3101 / 10000 := by
      have hlo : 613 / 2000 < x i := lt_of_not_ge (fun h => hsingle ⟨i, hi, h⟩)
      have hs : i ∈ smooth := by
        by_contra hn
        linarith [hrough i (hLI hi) hn]
      exact ⟨hs, hlo, lt_of_not_ge (fun h => hI ⟨i, hLI hi, hs, h⟩)⟩
    have hparts : (∑ i ∈ I \ L, x i) + (∑ i ∈ L, x i) = 1 := by
      rw [Finset.sum_sdiff hLI, hsum]
    have hnonneg : 0 ≤ ∑ i ∈ I \ L, x i :=
      Finset.sum_nonneg fun i hi => hpos i (Finset.mem_sdiff.mp hi).1
    have hlo : (L.card : ℝ) * (613 / 2000) ≤ ∑ i ∈ L, x i := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        Finset.sum_le_sum (fun i hi => (hband i hi).2.1.le)
    have hhi : (∑ i ∈ L, x i) ≤ (L.card : ℝ) * (3101 / 10000) := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        Finset.sum_le_sum (fun i hi => (hband i hi).2.2.le)
    have hcard : L.card = 3 := by
      have hlt : L.card < 4 := by
        by_contra! hn
        have hcast : (4 : ℝ) ≤ L.card := by exact_mod_cast hn
        linarith
      have hgt : 2 < L.card := by
        by_contra! hn
        have hcast : (L.card : ℝ) ≤ 2 := by exact_mod_cast hn
        linarith
      omega
    have hcast : (L.card : ℝ) = 3 := by exact_mod_cast hcard
    refine ⟨L, hLI, hcard, hband, by linarith, ?_⟩
    exact le_or_gt _ _ |>.imp_right fun h => ⟨h, lt_of_not_ge hsmall⟩
  · intro m r s hm hm' hr hs hs' hr'
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · intro ν r s hν hν' hr hs hr' hs'
    refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
    by_cases hdiag : r - s / 2 + ν ≤ 1 / 2 - ε
    · exact Or.inl hdiag
    · exact Or.inr ⟨by linarith, by linarith [lt_of_not_ge hdiag]⟩
  · intro a q r s ha hq hq' hr hr' hs hs'
    exact ⟨by linarith, by linarith, by linarith⟩

