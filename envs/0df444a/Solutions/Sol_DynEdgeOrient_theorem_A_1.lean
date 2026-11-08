-- Prove2me | solution 1 for DynEdgeOrient.theorem_A_1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T16:04:20.883739+00:00
-- url     : https://prove2.me/submissions/d14a6b11-a1f1-41ac-96ec-52d50c032c68

import Mathlib

/-- Log-sum inequality: `(∑ a) log((∑ a)/(∑ b)) ≤ ∑ a log(a/b)`. -/
theorem solution (n : ℕ) (a b : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hab : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) ≤
      ∑ i, a i * Real.log (a i / b i) := by
  classical
  set A := ∑ i, a i with hAdef
  set B := ∑ i, b i with hBdef
  by_cases hA : A = 0
  · have ha0 : ∀ i, a i = 0 := by
      intro i
      have hle : a i ≤ A := by
        rw [hAdef]
        exact Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
      linarith [ha i]
    simp [hA, ha0]
  · have hApos : 0 < A := lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => ha i)) (Ne.symm hA)
    have hBpos : 0 < B := by
      by_contra h
      have hB0 : B = 0 := le_antisymm (not_lt.mp h) (Finset.sum_nonneg (fun i _ => hb i))
      have hb0 : ∀ i, b i = 0 := by
        intro i
        have hle : b i ≤ B := by
          rw [hBdef]
          exact Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ i)
        linarith [hb i]
      have ha0 : ∀ i, a i = 0 := fun i => hab i (hb0 i)
      have : A = 0 := by simp [hAdef, ha0]
      exact hA this
    set S := Finset.univ.filter (fun i => 0 < a i) with hSdef
    have hzero : ∀ i, ¬ 0 < a i → a i = 0 := by
      intro i hi
      rcases lt_or_eq_of_le (ha i) with h | h
      · exact absurd h hi
      · exact h.symm
    have hbpos_of : ∀ i, 0 < a i → 0 < b i := by
      intro i hi
      rcases lt_or_eq_of_le (hb i) with h | h
      · exact h
      · exfalso
        have : a i = 0 := hab i h.symm
        linarith
    have hsumS : ∑ i ∈ S, a i = A := by
      rw [hAdef]
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i _ hi
      exact hzero i (by simpa [hSdef] using hi)
    have hF : ∀ i ∈ S, (a i / A) * Real.log ((b i * A) / (a i * B)) ≤
        b i / B - a i / A := by
      intro i hi
      have hapos : 0 < a i := (Finset.mem_filter.mp hi).2
      have hbpos : 0 < b i := hbpos_of i hapos
      have ht : 0 < (b i * A) / (a i * B) := by positivity
      have hlog := Real.log_le_sub_one_of_pos ht
      have hcoef : 0 < a i / A := div_pos hapos hApos
      have hmul := mul_le_mul_of_nonneg_left hlog hcoef.le
      have heq : (a i / A) * ((b i * A) / (a i * B) - 1) = b i / B - a i / A := by
        field_simp
      linarith
    have hsumle : ∑ i ∈ S, (a i / A) * Real.log ((b i * A) / (a i * B)) ≤ 0 := by
      have h1 := Finset.sum_le_sum hF
      have h2 : ∑ i ∈ S, (b i / B - a i / A) ≤ 0 := by
        rw [Finset.sum_sub_distrib]
        have hbdiv : ∑ i ∈ S, b i / B = (∑ i ∈ S, b i) / B := (Finset.sum_div ..).symm
        have hadiv : ∑ i ∈ S, a i / A = (∑ i ∈ S, a i) / A := (Finset.sum_div ..).symm
        rw [hbdiv, hadiv, hsumS, div_self hA]
        have hbS : ∑ i ∈ S, b i ≤ B := by
          rw [hBdef]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            (fun i _ _ => hb i)
        have hle1 : (∑ i ∈ S, b i) / B ≤ 1 := by
          rw [div_le_one hBpos]
          exact hbS
        linarith
      linarith
    have hsplit : ∑ i ∈ S, (a i / A) * Real.log ((b i * A) / (a i * B)) =
        (1 / A) * ∑ i ∈ S, a i * Real.log (b i / a i) + Real.log (A / B) := by
      have hterm : ∀ i ∈ S, (a i / A) * Real.log ((b i * A) / (a i * B)) =
          (a i / A) * Real.log (b i / a i) + (a i / A) * Real.log (A / B) := by
        intro i hi
        have hapos : 0 < a i := (Finset.mem_filter.mp hi).2
        have hbpos : 0 < b i := hbpos_of i hapos
        have harg : (b i * A) / (a i * B) = (b i / a i) * (A / B) := by
          field_simp
        rw [harg, Real.log_mul (by positivity) (by positivity)]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      have hfirst : ∑ i ∈ S, a i / A * Real.log (b i / a i) =
          1 / A * ∑ i ∈ S, a i * Real.log (b i / a i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      have hsecond : ∑ i ∈ S, a i / A * Real.log (A / B) = Real.log (A / B) := by
        rw [← Finset.sum_mul]
        have hsum : ∑ i ∈ S, a i / A = 1 := by
          rw [(Finset.sum_div ..).symm, hsumS, div_self hA]
        rw [hsum, one_mul]
      rw [hfirst, hsecond]
    have hT : ∑ i ∈ S, a i * Real.log (b i / a i) ≤ A * Real.log (B / A) := by
      have hle := hsumle
      rw [hsplit] at hle
      have hm := mul_le_mul_of_nonneg_left hle hApos.le
      have hAT : A * ((1 / A) * (∑ i ∈ S, a i * Real.log (b i / a i))) =
          ∑ i ∈ S, a i * Real.log (b i / a i) := by
        field_simp
      have hlogAB : Real.log (B / A) = -Real.log (A / B) := by
        rw [Real.log_div hBpos.ne' hApos.ne', Real.log_div hApos.ne' hBpos.ne']
        ring
      rw [hlogAB]
      nlinarith [hm, hAT]
    have hfun : ∀ i, a i * Real.log (a i / b i) = -(a i * Real.log (b i / a i)) := by
      intro i
      by_cases hai : a i = 0
      · simp [hai]
      · have hapos : 0 < a i := lt_of_le_of_ne (ha i) (Ne.symm hai)
        have hbpos : 0 < b i := hbpos_of i hapos
        rw [Real.log_div hapos.ne' hbpos.ne', Real.log_div hbpos.ne' hapos.ne']
        ring
    have hright : ∑ i, a i * Real.log (a i / b i) =
        -∑ i ∈ S, a i * Real.log (b i / a i) := by
      calc ∑ i, a i * Real.log (a i / b i)
          = ∑ i, -(a i * Real.log (b i / a i)) := Finset.sum_congr rfl (fun i _ => hfun i)
        _ = -(∑ i, a i * Real.log (b i / a i)) := by
              rw [Finset.sum_neg_distrib]
        _ = -(∑ i ∈ S, a i * Real.log (b i / a i)) := by
              congr 1
              symm
              apply Finset.sum_subset (Finset.subset_univ S)
              intro i _ hi
              have hai : a i = 0 := hzero i (by simpa [hSdef] using hi)
              simp [hai]
    rw [hright]
    have hlogAB' : Real.log (B / A) = -Real.log (A / B) := by
      rw [Real.log_div hBpos.ne' hApos.ne', Real.log_div hApos.ne' hBpos.ne']
      ring
    rw [hlogAB'] at hT
    nlinarith [hT]
