-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_public_original_intrinsic_mark_marginal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:52:16.148618+00:00
-- url     : https://prove2.me/submissions/f3157db5-8a84-4fff-b013-4e67b20de3ed

import Mathlib.MeasureTheory.Measure.GiryMonad
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_event_weighted_marked_count_is_measure
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_intrinsic_intensity_measure_complete

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original time-mark mean measure projects at unit time to its intrinsic mark intensity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ Q : Measure (ℝ≥0 × ℝ), ∃ markRate : Measure ℝ,
      (∀ C : Set (ℝ≥0 × ℝ), MeasurableSet C →
        Q C = (∫⁻ ω,
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            C ∂P)) ∧
      ((Q.restrict (Ioc 0 (1 : ℝ≥0) ×ˢ Set.univ)).map Prod.snd) = markRate ∧
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        Q (Ioc 0 T ×ˢ B) = (T : ℝ≥0∞) * markRate B) := by
  obtain ⟨Q, hQ⟩ :=
    avram_wave6_01_original_event_weighted_marked_count_is_measure
      X Set.univ MeasurableSet.univ
  obtain ⟨markRate, hRate, _, _, _⟩ :=
    avram_p2_c_borel_original_intrinsic_intensity_measure_complete X
  refine ⟨Q, markRate, ?_, ?_, ?_⟩
  · intro C hC
    simpa using hQ C hC
  · refine Measure.ext ?_
    intro B hB
    have hpre : MeasurableSet ((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) :=
      measurable_snd hB
    have hset : ((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) ∩
        (Ioc 0 (1 : ℝ≥0) ×ˢ Set.univ) = Ioc 0 (1 : ℝ≥0) ×ˢ B := by
      ext p
      simp
      tauto
    calc
      ((Q.restrict (Ioc 0 (1 : ℝ≥0) ×ˢ Set.univ)).map Prod.snd) B =
          (Q.restrict (Ioc 0 (1 : ℝ≥0) ×ˢ Set.univ))
            ((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) :=
              Measure.map_apply measurable_snd hB
      _ = Q (((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) ∩
          (Ioc 0 (1 : ℝ≥0) ×ˢ Set.univ)) := Measure.restrict_apply hpre
      _ = Q (Ioc 0 (1 : ℝ≥0) ×ˢ B) := by rw [hset]
      _ = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) := by
              simpa using hQ _ (measurableSet_Ioc.prod hB)
      _ = markRate B := by simpa using hRate 1 B hB
  · intro T B hB
    calc
      Q (Ioc 0 T ×ˢ B) =
          (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 T ×ˢ B) ∂P) := by
              simpa using hQ _ (measurableSet_Ioc.prod hB)
      _ = (T : ℝ≥0∞) * markRate B := hRate T B hB
