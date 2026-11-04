-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_negative_mark_mean_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:48:20.72358+00:00
-- url     : https://prove2.me/submissions/c87294c3-6fd2-49d2-ae99-8a2a4b5b7a9a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_event_weighted_marked_count_is_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Genuine original expected marked jump count is a measure on marks,
obtained by projecting the already established source time-mark mean measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) :
    ∃ μ : Measure ℝ, ∀ B : Set ℝ, MeasurableSet B →
      μ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) ∂P) := by
  obtain ⟨Q, hQ⟩ :=
    avram_wave6_01_original_event_weighted_marked_count_is_measure
      X Set.univ MeasurableSet.univ
  let μ : Measure ℝ := (Q.restrict (Ioc 0 T ×ˢ Set.univ)).map Prod.snd
  refine ⟨μ, ?_⟩
  intro B hB
  have hpre : MeasurableSet ((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) :=
    measurable_snd hB
  have hset : ((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) ∩
    (Ioc 0 T ×ˢ Set.univ) = Ioc 0 T ×ˢ B := by
      ext p
      simp
      tauto
  calc
    μ B = (Q.restrict (Ioc 0 T ×ˢ Set.univ))
      ((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) := by
        exact Measure.map_apply measurable_snd hB
    _ = Q (((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) ∩
      (Ioc 0 T ×ˢ Set.univ)) := by
        exact Measure.restrict_apply hpre
    _ = Q (Ioc 0 T ×ˢ B) := by rw [hset]
    _ = (∫⁻ ω in Set.univ, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) ∂P) :=
          hQ (Ioc 0 T ×ˢ B) (measurableSet_Ioc.prod hB)
    _ = _ := by simp
