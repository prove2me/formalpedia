-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_genuine_stopped_negative_levy_mark_crossing_discounted_zero_boundary_cash_at_most_w0
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:00:35.614008+00:00
-- url     : https://prove2.me/submissions/73046c95-fd99-4acd-bddf-66c9e94b9187

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_stopped_negative_levy_mark_genuine_ruin_crossing_count_at_most_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q)
    (w0 : ℝ) (hw0 : 0 ≤ w0) :
    let R : Set ℝ≥0 := {t |
      0 < t ∧ (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
      X.X t ω < Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ∧
      riskProcess X x D t ω < 0}
    (∑' t : ℝ≥0, if t ∈ R then
      Real.exp (-(q * (t : ℝ))) * w0 else 0) ≤ w0 := by
  intro R
  have hCard : R.encard ≤ 1 :=
    avram_bva_a22_original_stopped_negative_levy_mark_genuine_ruin_crossing_count_at_most_one
      X x D ω
  have hSub : R.Subsingleton :=
    Set.encard_le_one_iff_subsingleton.mp hCard
  rcases hSub.eq_empty_or_singleton with he | ⟨t, ht⟩
  · simpa [he] using hw0
  · have hQt : 0 ≤ q * (t : ℝ) :=
      mul_nonneg hq (NNReal.coe_nonneg t)
    have hExp : Real.exp (-(q * (t : ℝ))) ≤ 1 := by
      apply (Real.exp_le_one_iff).2
      linarith
    have hw : Real.exp (-(q * (t : ℝ))) * w0 ≤ w0 := by
      nlinarith [mul_le_mul_of_nonneg_right hExp hw0]
    simpa [ht] using hw
