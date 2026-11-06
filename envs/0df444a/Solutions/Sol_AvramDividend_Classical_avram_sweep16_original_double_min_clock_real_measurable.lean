-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_double_min_clock_real_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:45:54.274207+00:00
-- url     : https://prove2.me/submissions/d9bf3b0c-646f-4199-b987-cfbe4758a73f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ k, IsStoppingTime 𝓕.rightCont (S k))
    (τ : ℕ → Ω → ℝ≥0)
    (hτeq : ∀ k ω, τ k ω =
      (min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal) :
    ∀ k, Measurable (fun ω => (τ k ω : ℝ)) := by
  intro k
  have hRuin : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hD.1.1
  have hSM : Measurable (S k) := (hSstop k).measurable'
  have hMin : Measurable (fun ω =>
      min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)) :=
    (hRuin.min measurable_const).min hSM
  have hTNN : Measurable (fun ω =>
      (min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal) :=
    ENNReal.measurable_toNNReal.comp hMin
  have hTReal : Measurable (fun ω =>
      ((min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal : ℝ)) :=
    measurable_coe_nnreal_real.comp hTNN
  have hEq : (fun ω => (τ k ω : ℝ)) =
      (fun ω =>
        ((min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal : ℝ)) := by
    funext ω
    rw [hτeq k ω]
  rw [hEq]
  exact hTReal
