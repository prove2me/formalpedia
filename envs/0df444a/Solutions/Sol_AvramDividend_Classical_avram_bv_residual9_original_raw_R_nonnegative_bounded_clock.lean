-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_original_raw_R_nonnegative_bounded_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:22:25.920118+00:00
-- url     : https://prove2.me/submissions/75a3c533-1483-4b69-b39f-239b13a4d1f5

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_ae_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original BV raw remainder starts at zero and is nonnegative and monotone. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      R 0 = 0 ∧ ∀ t : ℝ≥0, t ≤ T → 0 ≤ R t ∧ R t ≤ R T := by
  have hmono :=
    AvramDividend.Classical.avram_bv_residual10_original_raw_R_ae_monotone X hBV
  filter_upwards [hmono] with ω hm
  dsimp only
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
    else 0
  let R : ℝ≥0 → ℝ := fun t =>
    ((t : ℝ) * X.drift - X.X t ω) - J t
  have hJ0 : J 0 = 0 := by
    change (∑' v : ℝ≥0, if 0 < v ∧ v ≤ (0 : ℝ≥0) then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else (0 : ℝ)) = 0
    have heq :
        (fun v : ℝ≥0 => if 0 < v ∧ v ≤ (0 : ℝ≥0) then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else (0 : ℝ)) = (fun _ => 0) := by
      funext v
      have h : ¬ (0 < v ∧ v ≤ (0 : ℝ≥0)) := by
        intro hv
        exact (not_lt_of_ge hv.2) hv.1
      simp only [h, ↓reduceIte]
    rw [heq]
    exact tsum_zero
  have hR0 : R 0 = 0 := by
    simp [R, hJ0, X.X_zero]
  refine ⟨hR0, ?_⟩
  intro t ht
  constructor
  · have hzt : (0 : ℝ≥0) ≤ t := bot_le
    have h := hm hzt
    change R 0 ≤ R t at h
    rw [hR0] at h
    exact h
  · have h := hm ht
    change R t ≤ R T at h
    exact h
