-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_actual_masked_history_survival_additive_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:16:52.623022+00:00
-- url     : https://prove2.me/submissions/d1e4e34d-f40e-4d74-889d-3a7403f93c88

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal
attribute [local instance] Classical.propDecidable

/-- Complete historical killing is equivalent to continuous survival on
the remaining original-clock window, once dead histories are encoded
by reserve -1. In particular no W(0)=0 boundary assumption is used. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (s T : ℝ≥0) (ω : Ω) :
    (∀ t : ℝ≥0, t ≤ s + T → 0 ≤ x + X.X t ω) ↔
    (∀ v : ℝ≥0, v ≤ T →
      0 ≤ (if ∀ w : ℝ≥0, w ≤ s → 0 ≤ x + X.X w ω
            then x + X.X s ω else (-1 : ℝ)) +
        (X.X (s + v) ω - X.X s ω)) := by
  classical
  let A : Prop := ∀ w : ℝ≥0, w ≤ s → 0 ≤ x + X.X w ω
  constructor
  · intro h v hv
    have hA : A := by
      intro w hw
      exact h w (le_trans hw (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ T from zero_le)))
    have hv' := h (s + v) (by
      simpa only [add_comm] using (add_le_add_left hv s))
    have hA' : ∀ w : ℝ≥0, w ≤ s → 0 ≤ x + X.X w ω := hA
    rw [if_pos hA']
    linarith
  · intro h
    have hA : A := by
      by_contra hn
      have hzero := h 0 (by simp)
      have hn' : ¬ (∀ w : ℝ≥0, w ≤ s → 0 ≤ x + X.X w ω) := hn
      simp [hn'] at hzero
      norm_num at hzero
    intro t ht
    rcases le_total t s with hts | hst
    · exact hA t hts
    · obtain ⟨v, rfl⟩ := exists_add_of_le hst
      have hv : v ≤ T := (add_le_add_iff_left s).mp ht
      have hf := h v hv
      have hA' : ∀ w : ℝ≥0, w ≤ s → 0 ≤ x + X.X w ω := hA
      have hf' : 0 ≤ (x + X.X s ω) +
          (X.X (s + v) ω - X.X s ω) := by
        simpa only [if_pos hA'] using hf
      linarith
