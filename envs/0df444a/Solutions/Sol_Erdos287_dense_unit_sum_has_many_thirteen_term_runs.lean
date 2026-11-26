-- Prove2me | solution 1 for Erdos287.dense_unit_sum_has_many_thirteen_term_runs
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T15:02:10.975796+00:00
-- url     : https://prove2.me/submissions/e8e0e128-e52b-404f-95d9-c314242d78a4

import Mathlib
import Theorems.Thm_Erdos287_weighted_consecutive_selected_windows

open Finset MeasureTheory

set_option autoImplicit false

private theorem log_ratio_bound : Real.log (2952 / 1000 : ℝ) < 108249 / 100000 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
  have h := Real.sum_le_exp_of_nonneg (show 0 ≤ (108249 / 100000 : ℝ) by norm_num) 10
  refine lt_of_lt_of_le ?_ h
  norm_num [sum_range_succ, Nat.factorial_succ]

/-- At endpoint ratio at most 2.952, a reciprocal sum of one forces at
least one fully selected thirteen-term window per 300 positions at scale. -/
theorem solution (D : Finset ℕ) (m M : ℕ) (hm : 1 < m) (hmM : m ≤ M)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℝ) / n = 1)
    (hscale : 1000000 ≤ M) (hratio : 1000 * M ≤ 2952 * m) :
    let R := (Finset.Icc (m + 12) M).filter (fun n => ∀ i ∈ Finset.range 13, n - i ∈ D)
    M < 300 * R.card := by
  classical
  let I := Icc m M
  let E := Icc (m + 12) M
  let R := E.filter (fun n => ∀ i ∈ range 13, n - i ∈ D)
  let w (n : ℕ) := (1 : ℝ) / n
  let H := ∑ n ∈ I, w n
  let x := m - 1
  have hxm : x + 1 = m := by dsimp [x]; omega
  have hx : 0 < x := by dsimp [x]; omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hH : H ≤ Real.log ((M : ℝ) / x) := by
    have himage : (Ico x M).image (fun z => z + 1) = I := by
      ext n
      simp only [mem_image, mem_Ico, mem_Icc, I]
      constructor
      · rintro ⟨z, ⟨hl, hh⟩, rfl⟩
        omega
      · rintro ⟨hl, hh⟩
        exact ⟨n - 1, ⟨by omega, by omega⟩, by omega⟩
    have ha : AntitoneOn (fun t : ℝ => 1 / t) (Set.Icc (x : ℝ) (M : ℝ)) := by
      intro a ha b _ hab
      exact one_div_le_one_div_of_le (hxR.trans_le ha.1) hab
    calc
      H = ∑ n ∈ Ico x M, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := by
        unfold H
        rw [← himage, sum_image (fun _ _ _ _ he => Nat.add_right_cancel he)]
      _ ≤ ∫ t in (x : ℝ)..(M : ℝ), 1 / t := AntitoneOn.sum_le_integral_Ico (by omega) ha
      _ = Real.log ((M : ℝ) / x) := integral_one_div_of_pos hxR hMR
  have hratioR : (M : ℝ) ≤ (2952 / 1000 : ℝ) * m := by
    have h : (1000 : ℝ) * M ≤ (2952 : ℝ) * m := by exact_mod_cast hratio
    linarith
  have hmcast : (x : ℝ) + 1 = m := by exact_mod_cast hxm
  have hlogTail : Real.log ((m : ℝ) / x) ≤ 1 / (x : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hmR hxR)
    convert h using 1
    rw [← hmcast, add_div, div_self hxR.ne']
    ring
  have hHbound : H ≤ 108249 / 100000 + 1 / (x : ℝ) := calc
    H ≤ Real.log ((M : ℝ) / x) := hH
    _ ≤ Real.log ((2952 / 1000 : ℝ) * ((m : ℝ) / x)) := by
      apply Real.log_le_log (div_pos hMR hxR)
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hratioR hxR.le
    _ = Real.log (2952 / 1000 : ℝ) + Real.log ((m : ℝ) / x) := by
      rw [Real.log_mul (by norm_num) (div_ne_zero hmR.ne' hxR.ne')]
    _ ≤ _ := add_le_add log_ratio_bound.le hlogTail
  have hEsub : E ⊆ I := fun n hn =>
    mem_Icc.mpr ⟨by have := (mem_Icc.mp hn).1; omega, (mem_Icc.mp hn).2⟩
  have hmissSub : I \ E ⊆ Ico m (m + 12) := by
    intro n hn
    obtain ⟨hi, he⟩ := mem_sdiff.mp hn
    have h := mem_Icc.mp hi
    exact mem_Ico.mpr ⟨h.1, lt_of_not_ge fun hlow => he (mem_Icc.mpr ⟨hlow, h.2⟩)⟩
  have hshort : (∑ n ∈ I \ E, w n) ≤ 12 / (m : ℝ) := calc
    _ ≤ ∑ n ∈ Ico m (m + 12), w n :=
      sum_le_sum_of_subset_of_nonneg hmissSub (fun _ _ _ => by dsimp [w]; positivity)
    _ ≤ ∑ _n ∈ Ico m (m + 12), (1 : ℝ) / m := by
      refine sum_le_sum fun n hn => one_div_le_one_div_of_le hmR ?_
      exact_mod_cast (mem_Ico.mp hn).1
    _ = _ := by simp [Nat.card_Ico, nsmul_eq_mul]; ring
  have hsplit : (∑ n ∈ I \ E, w n) + (∑ n ∈ E, w n) = H := sum_sdiff hEsub
  have hweighted := Erdos287.weighted_consecutive_selected_windows D m M 13 (by omega)
    (by decide) hD hsum
  change (∑ n ∈ E, w n) - (13 : ℝ) * (H - 1) ≤ ∑ n ∈ R, w n at hweighted
  have hRupper : (∑ n ∈ R, w n) ≤ R.card / (m : ℝ) := calc
    _ ≤ ∑ _n ∈ R, (1 : ℝ) / m := by
      refine sum_le_sum fun n hn => one_div_le_one_div_of_le hmR ?_
      exact_mod_cast (mem_Icc.mp (hEsub (mem_filter.mp hn).1)).1
    _ = _ := by simp [nsmul_eq_mul]; ring
  have hRlower : (13 : ℝ) - 12 * (108249 / 100000 + 1 / (x : ℝ)) - 12 / (m : ℝ) ≤
      (R.card : ℝ) / m := by linarith
  have hmul := (le_div_iff₀ hmR).mp hRlower
  have heq : ((13 : ℝ) - 12 * (108249 / 100000 + 1 / (x : ℝ)) - 12 / (m : ℝ)) * m =
      (253 / 25000 : ℝ) * m - 12 * ((m : ℝ) / x) - 12 := by
    field_simp [hxR.ne', hmR.ne']
    ring
  rw [heq] at hmul
  have hhalf : (m : ℝ) / x ≤ 2 := by
    apply (div_le_iff₀ hxR).mpr
    have hxone : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    linarith
  have hRfin : (253 / 25000 : ℝ) * m - 36 ≤ (R.card : ℝ) := by linarith
  have hlarge : (1000000 : ℝ) ≤ M := by exact_mod_cast hscale
  have hres : (M : ℝ) < (300 : ℝ) * R.card := by linarith only [hRfin, hratioR, hlarge]
  change M < 300 * R.card
  exact_mod_cast hres

