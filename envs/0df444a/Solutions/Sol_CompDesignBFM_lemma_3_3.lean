-- Prove2me | solution 1 for CompDesignBFM.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T16:18:05.754192+00:00
-- url     : https://prove2.me/submissions/8c09a8c7-2772-4b8a-a6e1-983271e39c77

import Mathlib

/-- CompDesignBFM Lemma 3.3: the product over all but a maximal coordinate is at least `e⁻¹`. -/
theorem solution {n : ℕ} (x : Fin n → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (hsum : ∑ i, x i ≤ 1) (i' : Fin n) (hi' : ∀ i, x i ≤ x i') :
    Real.exp (-1) ≤ ∏ i ∈ Finset.univ.erase i', (1 - x i) := by
  classical
  set T := Finset.univ.erase i' with hTdef
  have hpair : ∀ i, i ≠ i' → x i + x i' ≤ ∑ j, x j := by
    intro i hne
    have hsub : ({i, i'} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
    have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hx0 j)
    rw [Finset.sum_insert (by simpa [hne]), Finset.sum_singleton] at h
    linarith
  by_cases hxi' : x i' = 1
  · have hone : ∀ i ∈ T, x i = 0 := by
      intro i hi
      have hne : i ≠ i' := Finset.ne_of_mem_erase hi
      have hp := hpair i hne
      have hle1 : x i + x i' ≤ 1 := le_trans hp hsum
      have hxi0 : x i ≤ 0 := by
        have h1 : x i + 1 ≤ 1 := by simpa [hxi'] using hle1
        linarith
      exact le_antisymm hxi0 (hx0 i)
    have hprod : ∏ i ∈ T, (1 - x i) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      rw [hone i hi]
      ring
    rw [hprod]
    exact Real.exp_le_one_iff.mpr (by norm_num)
  · have hlt : x i' < 1 := lt_of_le_of_ne (hx1 i') hxi'
    have hden : 0 < 1 - x i' := by linarith
    have hper : ∀ i ∈ T, -(x i / (1 - x i)) ≤ Real.log (1 - x i) := by
      intro i hi
      have hxi : x i < 1 := lt_of_le_of_lt (hi' i) hlt
      have hpos : 0 < 1 - x i := by linarith
      have h := Real.one_sub_inv_le_log_of_pos hpos
      have heq : 1 - (1 - x i)⁻¹ = -(x i / (1 - x i)) := by
        field_simp
        ring
      linarith
    have hsum_bound : ∑ i ∈ T, x i / (1 - x i) ≤ 1 := by
      have hstep : ∑ i ∈ T, x i / (1 - x i) ≤ ∑ i ∈ T, x i / (1 - x i') := by
        apply Finset.sum_le_sum
        intro i hi
        exact div_le_div_of_nonneg_left (hx0 i) hden (by linarith [hi' i])
      have hsumT : ∑ i ∈ T, x i = (∑ i, x i) - x i' := by
        rw [hTdef]
        exact Finset.sum_erase_eq_sub (Finset.mem_univ i')
      have hnum : ∑ i ∈ T, x i ≤ 1 - x i' := by
        rw [hsumT]
        linarith
      calc ∑ i ∈ T, x i / (1 - x i) ≤ ∑ i ∈ T, x i / (1 - x i') := hstep
        _ = (∑ i ∈ T, x i) / (1 - x i') := by rw [Finset.sum_div]
        _ ≤ 1 := by
              rw [div_le_one hden]
              exact hnum
    have hsumlog : -1 ≤ ∑ i ∈ T, Real.log (1 - x i) := by
      have h := Finset.sum_le_sum hper
      rw [Finset.sum_neg_distrib] at h
      linarith
    calc Real.exp (-1) ≤ Real.exp (∑ i ∈ T, Real.log (1 - x i)) :=
          Real.exp_le_exp.mpr hsumlog
      _ = ∏ i ∈ T, Real.exp (Real.log (1 - x i)) := Real.exp_sum ..
      _ = ∏ i ∈ T, (1 - x i) := by
            apply Finset.prod_congr rfl
            intro i hi
            have hxi : x i < 1 := lt_of_le_of_lt (hi' i) hlt
            exact Real.exp_log (by linarith)
