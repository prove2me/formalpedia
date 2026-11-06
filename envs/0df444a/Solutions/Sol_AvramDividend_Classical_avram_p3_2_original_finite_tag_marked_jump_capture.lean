-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_finite_tag_marked_jump_capture
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:52:55.014607+00:00
-- url     : https://prove2.me/submissions/c3baa22e-fa8c-4fd2-bff3-e54479766672

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_source_nonlinear_jump_count_eq_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- An arbitrary finite collection of genuine original Lévy marked times
is counted exactly once by the original marked counting integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : Finset ℝ≥0)
    (hT : ∀ t ∈ T, 0 < t ∧
      X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p,
      (if p.1 ∈ (T : Set ℝ≥0) then F p else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      ∑ t ∈ T, F (t,
        X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t) := by
  classical
  have hM : MeasurableSet
      {p : ℝ≥0 × ℝ | p.1 ∈ (T : Set ℝ≥0)} :=
    T.measurableSet.preimage measurable_fst
  have hF' : Measurable
      (fun p : ℝ≥0 × ℝ => if p.1 ∈ (T : Set ℝ≥0) then F p else 0) :=
    Measurable.ite hM hF measurable_const
  rw [avram_p3_2_original_source_nonlinear_jump_count_eq_tsum X ω
    (fun p : ℝ≥0 × ℝ =>
      if p.1 ∈ (T : Set ℝ≥0) then F p else 0) hF']
  rw [tsum_eq_sum (s := T)]
  · apply Finset.sum_congr rfl
    intro t ht
    simp [ht, (hT t ht).1, (hT t ht).2]
  · intro t ht
    simp [ht]
