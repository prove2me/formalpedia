-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_centered_future_increment_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:50:14.372029+00:00
-- url     : https://prove2.me/submissions/ad30972d-f093-4b5d-b4ef-b6d2cd0ddbab

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_future_increment_L1_integrable_equal_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_future_increment_condExp_of_source_past_eq_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original centred future Lévy increment is a zero conditional-mean
martingale difference relative to its actual source filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hInt : Integrable (X.X t) P) :
    P[(fun ω => (X.X (s + t) ω - X.X s ω) -
      (∫ η, X.X t η ∂P)) | 𝓕 s] =ᵐ[P]
      (fun _ => (0 : ℝ)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let A : Ω → ℝ := fun ω => X.X (s + t) ω - X.X s ω
  let m : ℝ := ∫ η, X.X t η ∂P
  have hA : Integrable A P :=
    (avram_wave7_06_original_future_increment_L1_integrable_equal_mean
      X s t hInt).1
  have hC : Integrable (fun _ : Ω => m) P := integrable_const m
  have hSub :=
    condExp_sub hA hC (𝓕 s)
  have hOld :=
    avram_wave7_06_original_future_increment_condExp_of_source_past_eq_mean
      X s t hInt
  change P[A | 𝓕 s] =ᵐ[P] (fun _ : Ω => m) at hOld
  have hConst :
      P[(fun _ : Ω => m) | 𝓕 s] = (fun _ : Ω => m) :=
    condExp_const (𝓕.le s) m
  change P[(fun ω => A ω - m) | 𝓕 s] =ᵐ[P]
    (fun _ : Ω => (0 : ℝ))
  filter_upwards [hSub, hOld] with ω hs he
  calc
    P[(fun x => A x - m) | 𝓕 s] ω =
        (P[A | 𝓕 s] - P[(fun _ : Ω => m) | 𝓕 s]) ω := hs
    _ = (P[A | 𝓕 s] - fun _ : Ω => m) ω := by rw [hConst]
    _ = 0 := by simpa only [Pi.sub_apply, he, sub_self]
