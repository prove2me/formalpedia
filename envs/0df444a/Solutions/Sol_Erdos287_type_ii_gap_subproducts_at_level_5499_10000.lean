-- Prove2me | solution 1 for Erdos287.type_ii_gap_subproducts_at_level_5499_10000
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T21:31:30.446857+00:00
-- url     : https://prove2.me/submissions/99dee918-732c-47d0-a5e2-bfd3ee4f7539

import Mathlib

open Finset

set_option autoImplicit false

private theorem small_subproduct {ι : Type*} [DecidableEq ι] (x : ι → ℝ)
    (S : Finset ι) (hsmall : ∀ i ∈ S, x i < 1 / 100)
    (hsum : 1 / 100 ≤ ∑ i ∈ S, x i) :
    ∃ J ⊆ S, 1 / 100 ≤ ∑ i ∈ J, x i ∧ ∑ i ∈ J, x i ≤ 1 / 50 := by
  induction S using Finset.induction_on with
  | empty => norm_num at hsum
  | @insert i S hi ih =>
    by_cases htail : 1 / 100 ≤ ∑ j ∈ S, x j
    · obtain ⟨J, hJ, hlo, hhi⟩ :=
        ih (fun j hj => hsmall j (mem_insert_of_mem hj)) htail
      exact ⟨J, hJ.trans (subset_insert i S), hlo, hhi⟩
    · refine ⟨insert i S, Finset.Subset.refl _, hsum, ?_⟩
      rw [sum_insert hi]
      linarith [hsmall i (mem_insert_self i S)]

private theorem choose_block {ι : Type*} [DecidableEq ι] (I smooth : Finset ι) (x : ι → ℝ)
    (hpos : ∀ i ∈ I, 0 ≤ x i) (hsum : ∑ i ∈ I, x i = 1)
    (hrough : ∀ i ∈ I, i ∉ smooth → x i ≤ 3 / 10) :
    (∃ i ∈ I, i ∈ smooth ∧ 13 / 40 ≤ x i) ∨
      ∃ J ⊆ I, (1 / 100 ≤ ∑ i ∈ J, x i ∧ ∑ i ∈ J, x i ≤ 313 / 3125) ∨
        (1 / 8 ≤ ∑ i ∈ J, x i ∧ ∑ i ∈ J, x i ≤ 7501 / 25000) := by
  by_cases hI : ∃ i ∈ I, i ∈ smooth ∧ 13 / 40 ≤ x i
  · exact Or.inl hI
  right
  let S := I.filter fun i => x i < 1 / 100
  have hSI : S ⊆ I := filter_subset _ _
  by_cases hsmall : 1 / 100 ≤ ∑ i ∈ S, x i
  · obtain ⟨J, hJ, hlo, hhi⟩ := small_subproduct x S (fun _ hi => (mem_filter.mp hi).2) hsmall
    exact ⟨J, hJ.trans hSI, Or.inl ⟨hlo, by linarith⟩⟩
  by_contra hII
  let B := I.filter fun i => 7501 / 25000 < x i
  let G := I \ (S ∪ B)
  have hBI : B ⊆ I := filter_subset _ _
  have hGI : G ⊆ I := sdiff_subset
  have hSB : Disjoint S B := by
    apply disjoint_left.mpr
    intro i hs hb
    linarith [(mem_filter.mp hs).2, (mem_filter.mp hb).2]
  have hparts : (∑ i ∈ G, x i) + ((∑ i ∈ S, x i) + ∑ i ∈ B, x i) = 1 := by
    rw [← sum_union hSB, sum_sdiff (union_subset hSI hBI), hsum]
  have hBbounds (i : ι) (hi : i ∈ B) : 7501 / 25000 ≤ x i ∧ x i ≤ 13 / 40 := by
    refine ⟨(mem_filter.mp hi).2.le, ?_⟩
    by_cases hs : i ∈ smooth
    · exact le_of_lt (lt_of_not_ge fun h => hI ⟨i, hBI hi, hs, h⟩)
    · linarith [hrough i (hBI hi) hs]
  have hGbounds (i : ι) (hi : i ∈ G) : 313 / 3125 < x i ∧ x i < 1 / 8 := by
    have hiI := hGI hi
    have hn := (mem_sdiff.mp hi).2
    have hlo : 1 / 100 ≤ x i := by
      by_contra! h
      exact hn (mem_union_left _ (mem_filter.mpr ⟨hiI, h⟩))
    have hhi : x i ≤ 7501 / 25000 := by
      by_contra! h
      exact hn (mem_union_right _ (mem_filter.mpr ⟨hiI, h⟩))
    refine ⟨lt_of_not_ge ?_, lt_of_not_ge ?_⟩
    · intro h
      exact hII ⟨{i}, singleton_subset_iff.mpr hiI, Or.inl (by simpa using And.intro hlo h)⟩
    · intro h
      exact hII ⟨{i}, singleton_subset_iff.mpr hiI, Or.inr (by simpa using And.intro h hhi)⟩
  have hGcard : G.card ≤ 1 := by
    by_contra! h
    obtain ⟨i, j, hi, hj, hij⟩ := one_lt_card_iff.mp h
    refine hII ⟨{i, j}, ?_, Or.inr ?_⟩
    · intro k hk
      rcases mem_insert.mp hk with rfl | hk
      · exact hGI hi
      · obtain rfl := mem_singleton.mp hk
        exact hGI hj
    · rw [sum_pair hij]
      obtain ⟨hi₁, hi₂⟩ := hGbounds i hi
      obtain ⟨hj₁, hj₂⟩ := hGbounds j hj
      exact ⟨by linarith, by linarith⟩
  have hBlower : (B.card : ℝ) * (7501 / 25000) ≤ ∑ i ∈ B, x i := by
    simpa only [sum_const, nsmul_eq_mul] using sum_le_sum (fun i hi => (hBbounds i hi).1)
  have hBupper : (∑ i ∈ B, x i) ≤ (B.card : ℝ) * (13 / 40) := by
    simpa only [sum_const, nsmul_eq_mul] using sum_le_sum (fun i hi => (hBbounds i hi).2)
  have hSnonneg : 0 ≤ ∑ i ∈ S, x i := sum_nonneg fun i hi => hpos i (hSI hi)
  by_cases hG : G.Nonempty
  · obtain ⟨i, hi⟩ := hG
    have hGeq : G = {i} := by
      apply Subset.antisymm
      · intro j hj
        exact mem_singleton.mpr (card_le_one_iff.mp hGcard hj hi)
      · exact singleton_subset_iff.mpr hi
    rw [hGeq, sum_singleton] at hparts
    obtain ⟨hlo, hhi⟩ := hGbounds i hi
    have hcard : B.card ≤ 2 := by
      by_contra! h
      have hc : (3 : ℝ) ≤ B.card := by exact_mod_cast h
      linarith
    have hc : (B.card : ℝ) ≤ 2 := by exact_mod_cast hcard
    linarith
  · rw [not_nonempty_iff_eq_empty.mp hG, sum_empty, zero_add] at hparts
    have hcard : B.card ≤ 3 := by
      by_contra! h
      have hc : (4 : ℝ) ≤ B.card := by exact_mod_cast h
      linarith
    have hc : (B.card : ℝ) ≤ 3 := by exact_mod_cast hcard
    linarith

/-- A pair of factors in the gap can be placed in the regular Type II range. -/
theorem solution {ι : Type*} [DecidableEq ι] (I smooth : Finset ι) (x : ι → ℝ)
    (hpos : ∀ i ∈ I, 0 ≤ x i) (hsum : ∑ i ∈ I, x i = 1)
    (hrough : ∀ i ∈ I, i ∉ smooth → x i ≤ 3 / 10)
    (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ 1 / 10000000) :
    ((∃ i ∈ I, i ∈ smooth ∧ 13 / 40 ≤ x i) ∨
      ∃ J ⊆ I, (1 / 100 ≤ ∑ i ∈ J, x i ∧ ∑ i ∈ J, x i ≤ 313 / 3125) ∨
        (1 / 8 ≤ ∑ i ∈ J, x i ∧ ∑ i ∈ J, x i ≤ 7501 / 25000)) ∧
    (∀ m r s : ℝ, 13 / 40 ≤ m → m ≤ 1 → 0 ≤ r → 0 ≤ s →
      s ≤ m - ε → r ≤ 5499 / 10000 - m + 2 * ε →
      (s - m) / 2 ≤ -ε / 2 ∧ r + s / 2 + 1 / 2 ≤ 1 - ε ∧
      r + s / 4 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      3 * r / 4 + s / 2 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      r / 2 + s / 4 - 3 * m / 4 ≤ -ε) ∧
    (∀ ν q r s : ℝ, 1 / 100 ≤ ν → ν ≤ 313 / 3125 → 0 ≤ q → q ≤ ε →
      0 ≤ r → r ≤ 2813 / 6250 + ε → 0 ≤ s → s ≤ 4991 / 50000 + ε →
      2 * (r + q) + s ≤ 1 - ε ∧
      5 * ν / 2 + (r + q) + 5 * s / 2 ≤ 1 - ε ∧
      5 * ν / 4 + 3 * (r + q) / 2 + 2 * s ≤ 1 - ε ∧
      5 * ν + 4 * (r + q) + 5 * s - 1 ≤ 6 * ν + 2 * (r + q) + 5 * s) ∧
    (∀ ν r s : ℝ, 1 / 8 ≤ ν → ν ≤ 7501 / 25000 → 0 ≤ r → 0 ≤ s →
      r ≤ 5499 / 10000 - ν + 2 * ε → s ≤ ν - ε →
      2 * r + ν ≤ 1 - ε ∧ r / 2 + 5 * ν / 4 ≤ 1 / 2 - ε ∧
      3 * r / 4 + ν ≤ 1 / 2 - ε ∧ r + 3 * ν / 2 ≤ 1 - ε ∧
      (r - s / 2 + ν ≤ 1 / 2 - ε ∨
        r + s / 2 ≤ 1 / 2 - ε ∧ 7 * r / 4 + 5 * ν / 4 + s ≤ 1 - ε)) ∧
    2 / (5499 / 10000 : ℝ) < 91 / 25 := by
  refine ⟨choose_block I smooth x hpos hsum hrough, ?_, ?_, ?_, by norm_num⟩
  · intro m r s hm hm' hr hs hs' hr'
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · intro ν q r s hν hν' hq hq' hr hr' hs hs'
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · intro ν r s hν hν' hr hs hr' hs'
    refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
    by_cases hdiag : r - s / 2 + ν ≤ 1 / 2 - ε
    · exact Or.inl hdiag
    · exact Or.inr ⟨by linarith, by linarith [lt_of_not_ge hdiag]⟩

