-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger56_discounted_gaussian_characteristic_roots
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:50:05.594785+00:00
-- url     : https://prove2.me/submissions/d174f6a4-8fc9-4bab-86c5-8efad70352ce

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- A positive Gaussian variance and discount give opposite-sign characteristic roots. -/
theorem solution (a b q : ℝ) (ha : 0 < a) (hq : 0 < q) :
    ∃ r l : ℝ, 0 < r ∧ l < 0 ∧
      b = -a * (r + l) ∧ q = -a * r * l := by
  let d : ℝ := Real.sqrt (b ^ 2 + 4 * a * q)
  have had : 0 < 2 * a := by positivity
  have hane : a ≠ 0 := ne_of_gt ha
  have hdis : 0 ≤ b ^ 2 + 4 * a * q := by positivity
  have hdnon : 0 ≤ d := Real.sqrt_nonneg _
  have hd2 : d ^ 2 = b ^ 2 + 4 * a * q := Real.sq_sqrt hdis
  have hpos : b < d := by
    by_contra h
    have hbd : d ≤ b := le_of_not_gt h
    have hbnon : 0 ≤ b := le_trans hdnon hbd
    have hprod : 0 ≤ (b - d) * (b + d) :=
      mul_nonneg (sub_nonneg.mpr hbd) (add_nonneg hbnon hdnon)
    nlinarith [mul_pos ha hq]
  have hneg : -b < d := by
    by_contra h
    have hbd : d ≤ -b := le_of_not_gt h
    have hbnon : 0 ≤ -b := le_trans hdnon hbd
    have hprod : 0 ≤ (-b - d) * (-b + d) :=
      mul_nonneg (sub_nonneg.mpr hbd) (add_nonneg hbnon hdnon)
    nlinarith [mul_pos ha hq]
  refine ⟨(d - b) / (2 * a), (-d - b) / (2 * a), ?_, ?_, ?_, ?_⟩
  · exact div_pos (sub_pos.mpr hpos) had
  · exact div_neg_of_neg_of_pos (by linarith [hneg]) had
  · field_simp [hane]
    ring
  · calc
      q = (b ^ 2 - d ^ 2) / (-4 * a) := by
        rw [hd2]
        field_simp [hane]
        ring
      _ = -a * ((d - b) / (2 * a)) * ((-d - b) / (2 * a)) := by
        field_simp [hane]
        ring
