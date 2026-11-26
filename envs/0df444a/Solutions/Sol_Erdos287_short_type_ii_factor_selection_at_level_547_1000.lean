-- Prove2me | solution 1 for Erdos287.short_type_ii_factor_selection_at_level_547_1000
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T21:13:12.664394+00:00
-- url     : https://prove2.me/submissions/4e624c8f-7ab3-4087-8770-bae380525ada

import Mathlib

set_option autoImplicit false

private theorem small_subproduct {ι : Type*} [DecidableEq ι]
    (x : ι → ℝ) (S : Finset ι) (hsmall : ∀ i ∈ S, x i < 1 / 100)
    (hsum : 1 / 100 ≤ ∑ i ∈ S, x i) :
    ∃ J ⊆ S, 1 / 100 ≤ ∑ i ∈ J, x i ∧ ∑ i ∈ J, x i ≤ 1509 / 5000 := by
  induction S using Finset.induction_on with
  | empty => norm_num at hsum
  | @insert i S hi ih =>
    by_cases htail : 1 / 100 ≤ ∑ j ∈ S, x j
    · obtain ⟨J, hJ, hlo, hhi⟩ :=
        ih (fun j hj => hsmall j (Finset.mem_insert_of_mem hj)) htail
      exact ⟨J, hJ.trans (Finset.subset_insert i S), hlo, hhi⟩
    · refine ⟨insert i S, Finset.Subset.refl _, hsum, ?_⟩
      rw [Finset.sum_insert hi]
      linarith [hsmall i (Finset.mem_insert_self i S)]

/-- Short-factor Type II closes the arithmetic box split at level 547/1000
and continues to do so with the corrected last spectral term. -/
theorem solution {ι : Type*} [DecidableEq ι] (I smooth : Finset ι) (x : ι → ℝ)
    (hpos : ∀ i ∈ I, 0 ≤ x i) (hsum : ∑ i ∈ I, x i = 1)
    (hrough : ∀ i ∈ I, i ∉ smooth → x i ≤ 251 / 1000)
    (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ 1 / 1000000) :
    ((∃ i ∈ I, i ∈ smooth ∧ 1603 / 5000 ≤ x i) ∨
      ∃ J ⊆ I, 1 / 100 ≤ ∑ i ∈ J, x i ∧ ∑ i ∈ J, x i ≤ 1509 / 5000) ∧
    (∀ m r s : ℝ, 1603 / 5000 ≤ m → m ≤ 1 → 0 ≤ r → 0 ≤ s →
      s ≤ m - ε → r ≤ 547 / 1000 - m + 2 * ε →
      (s - m) / 2 ≤ -ε / 2 ∧ r + s / 2 + 1 / 2 ≤ 1 - ε ∧
      r + s / 4 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      3 * r / 4 + s / 2 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      r / 2 + s / 4 - 3 * m / 4 ≤ -ε) ∧
    (∀ ν q r s : ℝ, 1 / 100 ≤ ν → ν ≤ 13 / 125 → 0 ≤ q → q ≤ ε →
      0 ≤ r → r ≤ 181 / 400 + ε → 0 ≤ s → s ≤ 189 / 2000 + ε →
      2 * (r + q) + s ≤ 1 - ε ∧
      5 * ν / 2 + (r + q) + 5 * s / 2 ≤ 1 - ε ∧
      5 * ν / 4 + 3 * (r + q) / 2 + 2 * s ≤ 1 - ε ∧
      5 * ν + 4 * (r + q) + 5 * s - 1 ≤ 6 * ν + 2 * (r + q) + 5 * s) ∧
    (∀ ν r s : ℝ, 13 / 125 ≤ ν → ν ≤ 1509 / 5000 → 0 ≤ r → 0 ≤ s →
      r ≤ 547 / 1000 - ν + 2 * ε → s ≤ ν - ε →
      2 * r + ν ≤ 1 - ε ∧ r / 2 + 5 * ν / 4 ≤ 1 / 2 - ε ∧
      3 * r / 4 + ν ≤ 1 / 2 - ε ∧ r + 3 * ν / 2 ≤ 1 - ε ∧
      (r - s / 2 + ν ≤ 1 / 2 - ε ∨
        r + s / 2 ≤ 1 / 2 - ε ∧ 7 * r / 4 + 5 * ν / 4 + s ≤ 1 - ε)) ∧
    2 / (547 / 1000 : ℝ) < 11 / 3 ∧ 8 / (3 : ℝ) < Real.exp 1 := by
  refine ⟨?_, ?_, ?_, ?_, by norm_num, by linarith [Real.exp_one_gt_d9]⟩
  · by_cases hI : ∃ i ∈ I, i ∈ smooth ∧ 1603 / 5000 ≤ x i
    · exact Or.inl hI
    right
    let L := I.filter fun i => 1 / 100 ≤ x i
    have hLI : L ⊆ I := Finset.filter_subset _ _
    by_cases hsingle : ∃ i ∈ L, x i ≤ 1509 / 5000
    · obtain ⟨i, hi, hhi⟩ := hsingle
      have hlo := (Finset.mem_filter.mp hi).2
      exact ⟨{i}, Finset.singleton_subset_iff.mpr (hLI hi),
        by simpa using hlo, by simpa using hhi⟩
    have hshort (i : ι) (hi : i ∈ I \ L) : x i < 1 / 100 := by
      obtain ⟨hiI, hiL⟩ := Finset.mem_sdiff.mp hi
      exact lt_of_not_ge fun h => hiL (Finset.mem_filter.mpr ⟨hiI, h⟩)
    by_cases hsmall : 1 / 100 ≤ ∑ i ∈ I \ L, x i
    · obtain ⟨J, hJ, hlo, hhi⟩ := small_subproduct x (I \ L) hshort hsmall
      exact ⟨J, hJ.trans Finset.sdiff_subset, hlo, hhi⟩
    exfalso
    have hband (i : ι) (hi : i ∈ L) : 1509 / 5000 ≤ x i ∧ x i ≤ 1603 / 5000 := by
      have hlo : 1509 / 5000 < x i := lt_of_not_ge (fun h => hsingle ⟨i, hi, h⟩)
      have hs : i ∈ smooth := by
        by_contra hn
        linarith [hrough i (hLI hi) hn]
      exact ⟨hlo.le, (lt_of_not_ge (fun h => hI ⟨i, hLI hi, hs, h⟩)).le⟩
    have hparts : (∑ i ∈ I \ L, x i) + (∑ i ∈ L, x i) = 1 := by
      rw [Finset.sum_sdiff hLI, hsum]
    have hnonneg : 0 ≤ ∑ i ∈ I \ L, x i :=
      Finset.sum_nonneg fun i hi => hpos i (Finset.mem_sdiff.mp hi).1
    have hlo : (L.card : ℝ) * (1509 / 5000) ≤ ∑ i ∈ L, x i := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        Finset.sum_le_sum (fun i hi => (hband i hi).1)
    have hhi : (∑ i ∈ L, x i) ≤ (L.card : ℝ) * (1603 / 5000) := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        Finset.sum_le_sum (fun i hi => (hband i hi).2)
    have hcard : L.card ≤ 3 := by
      by_contra! hn
      have hcast : (4 : ℝ) ≤ L.card := by exact_mod_cast hn
      linarith
    have hcast : (L.card : ℝ) ≤ 3 := by exact_mod_cast hcard
    linarith
  · intro m r s hm hm' hr hs hs' hr'
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · intro ν q r s hν hν' hq hq' hr hr' hs hs'
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · intro ν r s hν hν' hr hs hr' hs'
    refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
    by_cases hdiag : r - s / 2 + ν ≤ 1 / 2 - ε
    · exact Or.inl hdiag
    · exact Or.inr ⟨by linarith, by linarith [lt_of_not_ge hdiag]⟩

