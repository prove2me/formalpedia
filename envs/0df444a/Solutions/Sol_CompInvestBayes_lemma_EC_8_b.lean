-- Prove2me | solution 1 for CompInvestBayes.lemma_EC_8_b
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:36:22.280796+00:00
-- url     : https://prove2.me/submissions/0307efbe-c7ef-4096-b260-da8397b1fd8d

import Mathlib
import Definitions.Def_CompInvestBayes_closedForms

open CompInvestBayes in
theorem solution (p : Params) (hp : p.Standing) {y0 : ℝ} (hy0 : y0 ∈ Set.Icc (0 : ℝ) 1) :
    (p.c1 * p.lam < y0 → ∀ S1 : ℝ, 0 ≤ S1 → S1 ≠ p.mu1H → H0 p S1 y0 < H0 p p.mu1H y0) ∧
      (y0 < p.c1 * p.lam → ∀ S1 : ℝ, 0 ≤ S1 → S1 ≠ p.mu1L → H0 p S1 y0 < H0 p p.mu1L y0) ∧
      (y0 = p.c1 * p.lam → ∀ S1 : ℝ, 0 ≤ S1 → H0 p S1 y0 ≤ H0 p p.mu1L y0) := by
  obtain ⟨hy00, hy01⟩ := hy0
  have hl := hp.lam_pos
  have hab := hp.mu1L_lt_mu1H
  have hk1 : p.c1 * p.lam < 1 := (lt_div_iff₀ hl).mp hp.c1_lt
  have hk0 : 0 < p.c1 * p.lam := mul_pos hp.c1_pos hl
  set k := p.c1 * p.lam with hk
  have key : ∀ S, p.lam * H0 p S y0 =
      y0 * min S p.mu1H + (1 - y0) * min S p.mu1L - k * S := by
    intro S
    unfold H0
    rw [hk]
    have := hl.ne'
    first | (field_simp; ring) | field_simp | ring
  have Lb : p.lam * H0 p p.mu1H y0 = y0 * p.mu1H + (1 - y0) * p.mu1L - k * p.mu1H := by
    rw [key, min_self, min_eq_right hab.le]
  have La : p.lam * H0 p p.mu1L y0 = p.mu1L - k * p.mu1L := by
    rw [key, min_eq_left hab.le, min_self]; ring
  refine ⟨fun hy S hS hne => ?_, fun hy S hS hne => ?_, fun hy S hS => ?_⟩
  · apply lt_of_mul_lt_mul_left _ hl.le
    rw [Lb, key]
    rcases le_total S p.mu1L with h1 | h1
    · rw [min_eq_left (h1.trans hab.le), min_eq_left h1]
      nlinarith [mul_pos (sub_pos.mpr hy) (show 0 < p.mu1H - S by linarith),
        mul_nonneg (sub_nonneg.mpr hy01) (sub_nonneg.mpr h1)]
    · rcases le_total S p.mu1H with h2 | h2
      · have h2' : S < p.mu1H := lt_of_le_of_ne h2 hne
        rw [min_eq_left h2, min_eq_right h1]
        nlinarith [mul_pos (sub_pos.mpr hy) (sub_pos.mpr h2')]
      · have h2' : p.mu1H < S := lt_of_le_of_ne h2 (Ne.symm hne)
        rw [min_eq_right h2, min_eq_right h1]
        nlinarith [mul_pos hk0 (sub_pos.mpr h2')]
  · apply lt_of_mul_lt_mul_left _ hl.le
    rw [La, key]
    rcases le_total S p.mu1L with h1 | h1
    · have h1' : S < p.mu1L := lt_of_le_of_ne h1 hne
      rw [min_eq_left (h1.trans hab.le), min_eq_left h1]
      nlinarith [mul_pos (sub_pos.mpr hk1) (sub_pos.mpr h1')]
    · have h1' : p.mu1L < S := lt_of_le_of_ne h1 (Ne.symm hne)
      rcases le_total S p.mu1H with h2 | h2
      · rw [min_eq_left h2, min_eq_right h1]
        nlinarith [mul_pos (sub_pos.mpr hy) (sub_pos.mpr h1')]
      · rw [min_eq_right h2, min_eq_right h1]
        nlinarith [mul_pos (sub_pos.mpr hy) (sub_pos.mpr hab),
          mul_nonneg hk0.le (sub_nonneg.mpr h2)]
  · apply le_of_mul_le_mul_left _ hl
    rw [La, key]
    rcases le_total S p.mu1L with h1 | h1
    · rw [min_eq_left (h1.trans hab.le), min_eq_left h1]
      nlinarith [mul_nonneg (sub_nonneg.mpr hk1.le) (sub_nonneg.mpr h1)]
    · rcases le_total S p.mu1H with h2 | h2
      · rw [min_eq_left h2, min_eq_right h1, hy]
        nlinarith
      · rw [min_eq_right h2, min_eq_right h1, hy]
        nlinarith [mul_nonneg hk0.le (sub_nonneg.mpr h2)]
