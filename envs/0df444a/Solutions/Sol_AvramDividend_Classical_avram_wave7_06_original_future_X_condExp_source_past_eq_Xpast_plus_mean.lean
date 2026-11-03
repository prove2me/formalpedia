-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_future_X_condExp_source_past_eq_Xpast_plus_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:03:24.945893+00:00
-- url     : https://prove2.me/submissions/ca29fbe2-c3ac-46fd-aad2-a76e3c636a16

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_future_increment_L1_integrable_equal_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_future_increment_condExp_of_source_past_eq_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original source process future conditional expectation equals the actual
past state plus the genuine mean future increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hStart : Integrable (X.X s) P)
    (hFuture : Integrable (X.X t) P) :
    P[X.X (s + t) | 𝓕 s] =ᵐ[P]
      (fun ω => X.X s ω + (∫ η, X.X t η ∂P)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let A : Ω → ℝ := fun ω => X.X (s + t) ω - X.X s ω
  have hA : Integrable A P :=
    (avram_wave7_06_original_future_increment_L1_integrable_equal_mean
      X s t hFuture).1
  have hPastSM : StronglyMeasurable[𝓕 s] (X.X s) :=
    (X.adapted.measurable_le (le_refl s)).stronglyMeasurable
  have hPastCond :
      P[X.X s | 𝓕 s] = X.X s :=
    condExp_of_stronglyMeasurable (𝓕.le s) hPastSM hStart
  have hFutureCond :=
    avram_wave7_06_original_future_increment_condExp_of_source_past_eq_mean
      X s t hFuture
  change P[A | 𝓕 s] =ᵐ[P]
    (fun _ : Ω => ∫ η, X.X t η ∂P) at hFutureCond
  have hAdd :=
    condExp_add hA hStart (𝓕 s)
  have hEndEq :
      (fun ω => A ω + X.X s ω) = X.X (s + t) := by
    funext ω
    dsimp [A]
    ring
  change P[(fun ω => A ω + X.X s ω) | 𝓕 s] =ᵐ[P]
    P[A | 𝓕 s] + P[X.X s | 𝓕 s] at hAdd
  rw [hEndEq, hPastCond] at hAdd
  filter_upwards [hAdd, hFutureCond] with ω hCE hMean
  simpa only [Pi.add_apply, hMean, add_comm] using hCE
