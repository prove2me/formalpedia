-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_turn16_two_real_characteristic_roots_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:43:01.15834+00:00
-- url     : https://prove2.me/submissions/23e5eb7f-1bfb-40f4-80a9-1987920f93bb

import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal


noncomputable section

theorem solution
    (a c q : ℝ) (ha : 0 < a) (hq : 0 < q) :
    ∃ rpos rneg : ℝ, 0 < rpos ∧ rneg < 0 ∧
      a * (rpos + rneg) = -c ∧ a * (rpos * rneg) = -q := by
  let Δ : ℝ := c ^ 2 + 4 * a * q
  have hΔ : 0 ≤ Δ := by
    dsimp [Δ]
    positivity
  let d : ℝ := Real.sqrt Δ
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hdsq : d ^ 2 = Δ := by
    simpa [d] using Real.sq_sqrt hΔ
  have hstrict : c ^ 2 < d ^ 2 := by
    dsimp [Δ] at hdsq
    nlinarith [mul_pos ha hq]
  have hhigh : c < d := by
    by_contra hh
    have hdc : d ≤ c := le_of_not_gt hh
    have hcp : 0 ≤ c := le_trans hd hdc
    have hprod : 0 ≤ (c - d) * (c + d) :=
      mul_nonneg (sub_nonneg.mpr hdc) (add_nonneg hcp hd)
    nlinarith
  have hlow : -d < c := by
    by_contra hh
    have hcd : c ≤ -d := le_of_not_gt hh
    have hnegc : 0 ≤ -c := by linarith
    have hprod : 0 ≤ (-c - d) * (-c + d) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hden : 0 < 2 * a := by positivity
  have hfactor : (-c + d) * (-c - d) = -4 * a * q := by
    dsimp [Δ] at hdsq
    nlinarith
  refine ⟨(-c + d) / (2 * a), (-c - d) / (2 * a), ?_, ?_, ?_, ?_⟩
  · exact div_pos (by linarith) hden
  · exact div_neg_of_neg_of_pos (by linarith) hden
  · field_simp [ne_of_gt ha]
    ring
  · calc
      a * (((-c + d) / (2 * a)) * ((-c - d) / (2 * a))) =
          ((-c + d) * (-c - d)) / (4 * a) := by
            field_simp [ne_of_gt ha]
            ring
      _ = -q := by
        rw [hfactor]
        field_simp [ne_of_gt ha] <;> ring
