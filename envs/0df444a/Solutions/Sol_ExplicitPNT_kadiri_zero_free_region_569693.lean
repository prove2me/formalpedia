-- Prove2me | solution 1 for ExplicitPNT.kadiri_zero_free_region_569693
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T15:13:59.329604+00:00
-- url     : https://prove2.me/submissions/873fb4b2-2c2f-4bbc-8f60-d83c996325d7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

import Theorems.Thm_ExplicitPNT_rosser_schoenfeld_zero_free_region_9645908801
import Theorems.Thm_ExplicitPNT_riemann_hypothesis_up_to_3330657430697
import Theorems.Thm_ExplicitPNT_kadiri_zero_gap_iteration_table

set_option maxHeartbeats 600000

namespace KadiriReduction

lemma nonvanishing_of_zero_gap (R : ℝ) (hR : 5 ≤ R)
    (hRH : ∀ s : ℂ, 0 < s.re → s.re < 1 → 0 < s.im →
      s.im ≤ (3330657430697 / 1000 : ℝ) → riemannZeta s = 0 → s.re = 1 / 2)
    (hgap : ∀ s : ℂ, 0 < s.re → s.re < 1 →
      (3330657430697 / 1000 : ℝ) < s.im → riemannZeta s = 0 →
      (1 - s.re) * Real.log s.im ≤ (1 / 5 : ℝ) →
      1 / R < (1 - s.re) * Real.log s.im) :
    ∀ s : ℂ, 2 ≤ s.im →
      1 - 1 / (R * Real.log s.im) ≤ s.re → riemannZeta s ≠ 0 := by
  intro s ht hσ hz
  have hRp : 0 < R := by linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog : (1 / 2 : ℝ) ≤ Real.log s.im := hlog2.trans
    (Real.log_le_log (by norm_num) ht)
  have hlogp : 0 < Real.log s.im := by linarith
  have hden : 2 < R * Real.log s.im := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hlog)]
  have hinv : 1 / (R * Real.log s.im) < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ (mul_pos hRp hlogp)).2
    linarith
  have hrehalf : (1 / 2 : ℝ) < s.re := by linarith
  have hre0 : 0 < s.re := by linarith
  have hre1 : s.re < 1 :=
    lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hz)
  by_cases hT : s.im ≤ (3330657430697 / 1000 : ℝ)
  · have hcrit := hRH s hre0 hre1 (by linarith) hT hz
    linarith
  · have hbound : (1 - s.re) * Real.log s.im ≤ 1 / R := by
      calc
        (1 - s.re) * Real.log s.im ≤ (1 / (R * Real.log s.im)) * Real.log s.im :=
          mul_le_mul_of_nonneg_right (by linarith) hlogp.le
        _ = 1 / R := by field_simp
    have hRinv : 1 / R ≤ (1 / 5 : ℝ) := by
      apply (div_le_div_iff₀ hRp (by norm_num : (0 : ℝ) < 5)).2
      linarith
    have hstrict := hgap s hre0 hre1 (lt_of_not_ge hT) hz (hbound.trans hRinv)
    linarith

lemma reflect_positive_region (R : ℝ)
    (hpositive : ∀ s : ℂ, 2 ≤ s.im →
      1 - 1 / (R * Real.log s.im) ≤ s.re → riemannZeta s ≠ 0)
    (s : ℂ) (ht : 2 ≤ |s.im|)
    (hσ : 1 - 1 / (R * Real.log |s.im|) ≤ s.re) :
    riemannZeta s ≠ 0 := by
  by_cases him : 0 ≤ s.im
  · rw [abs_of_nonneg him] at ht hσ
    exact hpositive s ht hσ
  · have ht' : 2 ≤ (starRingEnd ℂ s).im := by
      simpa only [Complex.conj_im, abs_of_neg (lt_of_not_ge him)] using ht
    have hσ' : 1 - 1 / (R * Real.log (starRingEnd ℂ s).im) ≤ (starRingEnd ℂ s).re := by
      simpa only [Complex.conj_im, Complex.conj_re, abs_of_neg (lt_of_not_ge him)] using hσ
    intro hz
    apply hpositive (starRingEnd ℂ s) ht' hσ'
    simpa only [riemannZeta_conj, hz, map_zero]

end KadiriReduction

theorem solution (s : ℂ)
    (ht : 2 ≤ |s.im|)
    (hσ : 1 - 1 / ((569693 / 100000 : ℝ) * Real.log |s.im|) ≤ s.re) :
    riemannZeta s ≠ 0 := by
  have hRH := ExplicitPNT.riemann_hypothesis_up_to_3330657430697
  have improve (R r R' : ℝ) (hR' : 5 ≤ R')
      (hrow : (R = (9645908801 / 1000000000 : ℝ) ∧ r = (593943 / 100000 : ℝ) ∧ R' = (593944 / 100000 : ℝ)) ∨
      (R = (593944 / 100000 : ℝ) ∧ r = (571998 / 100000 : ℝ) ∧ R' = (571999 / 100000 : ℝ)) ∨
      (R = (571999 / 100000 : ℝ) ∧ r = (569918 / 100000 : ℝ) ∧ R' = (569919 / 100000 : ℝ)) ∨
      (R = (569919 / 100000 : ℝ) ∧ r = (569714 / 100000 : ℝ) ∧ R' = (569715 / 100000 : ℝ)) ∨
      (R = (569715 / 100000 : ℝ) ∧ r = (569694 / 100000 : ℝ) ∧ R' = (569695 / 100000 : ℝ)) ∨
      (R = (569695 / 100000 : ℝ) ∧ r = (569692 / 100000 : ℝ) ∧ R' = (569693 / 100000 : ℝ)))
      (hprevious : ∀ z : ℂ, 2 ≤ z.im →
        1 - 1 / (R * Real.log z.im) ≤ z.re → riemannZeta z ≠ 0) :
      ∀ z : ℂ, 2 ≤ z.im →
        1 - 1 / (R' * Real.log z.im) ≤ z.re → riemannZeta z ≠ 0 := by
    apply KadiriReduction.nonvanishing_of_zero_gap R' hR' hRH
    intro ρ h0 h1 hγ hz hnear
    exact ExplicitPNT.kadiri_zero_gap_iteration_table R r R' hrow hRH hprevious
      ρ h0 h1 hγ hz hnear
  have h0 := ExplicitPNT.rosser_schoenfeld_zero_free_region_9645908801
  have h1 := improve (9645908801 / 1000000000) (593943 / 100000) (593944 / 100000)
    (by norm_num) (Or.inl ⟨rfl, rfl, rfl⟩) h0
  have h2 := improve (593944 / 100000) (571998 / 100000) (571999 / 100000)
    (by norm_num) (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) h1
  have h3 := improve (571999 / 100000) (569918 / 100000) (569919 / 100000)
    (by norm_num) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))) h2
  have h4 := improve (569919 / 100000) (569714 / 100000) (569715 / 100000)
    (by norm_num) (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))) h3
  have h5 := improve (569715 / 100000) (569694 / 100000) (569695 / 100000)
    (by norm_num) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))) h4
  have h6 := improve (569695 / 100000) (569692 / 100000) (569693 / 100000)
    (by norm_num) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))) h5
  exact KadiriReduction.reflect_positive_region _ h6 s ht hσ

