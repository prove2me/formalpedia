-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_ruin_clipped_natural_clock_real_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:37:07.728208+00:00
-- url     : https://prove2.me/submissions/0f871449-6d0c-4dc1-bf7d-92d2c5f77c29

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_clock_real_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) :
    Measurable (fun ω : Ω =>
      (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ)) := by
  let τ : ℕ → Ω → ℝ≥0 := fun _ ω =>
    (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
  have hSstop : ∀ k : ℕ, IsStoppingTime 𝓕.rightCont
      (fun _ : Ω => (n : ℝ≥0∞)) := by
    intro k
    exact isStoppingTime_const 𝓕.rightCont (n : ℝ≥0)
  have hτ : ∀ k ω, τ k ω =
      (min (min (ruinTime X x D ω) (n : ℝ≥0∞))
        ((fun _ (_ : Ω) => (n : ℝ≥0∞)) k ω)).toNNReal := by
    intro k ω
    simp [τ, min_assoc]
  have hMeas :=
    avram_sweep16_original_double_min_clock_real_measurable
      X x C D hD n
      (fun _ (_ : Ω) => (n : ℝ≥0∞)) hSstop
      τ hτ 0
  simpa only [τ] using hMeas
