-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_filtered_gate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:53:55.250894+00:00
-- url     : https://prove2.me/submissions/52b90a17-6fcf-4045-8574-a05c700b0938

import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Process.Adapted
import Theorems.Thm_ProbabilityTheory_increment_apply
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_modified_levy_source
import Theorems.Thm_AvramDividend_Classical_avram_e0_natural_filtration_from_leanlevy_increment
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_LeanLevy_Processes_LevyProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (hraw : IsLevyProcess
      (fun t : ℝ≥0 => LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ)) P) :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (Z : ℝ≥0 → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ),
      (∀ ω, Z 0 ω = 0) ∧
      (∀ ω t, ContinuousWithinAt (fun s => Z s ω) (Ici t) t) ∧
      (∀ ω t, 0 < t →
        ∃ l, Tendsto (fun s => Z s ω) (nhdsWithin t (Iio t)) (nhds l)) ∧
      (∀ ω t l, 0 < t →
        Tendsto (fun s => Z s ω) (nhdsWithin t (Iio t)) (nhds l) →
        Z t ω ≤ l) ∧
      Adapted 𝓕 Z ∧
      (∀ s t, s ≤ t →
        Indep (MeasurableSpace.comap
          (fun ω => Z t ω - Z s ω) inferInstance) (𝓕 s) P) ∧
      (∀ s t, s ≤ t →
        IdentDistrib (fun ω => Z t ω - Z s ω)
          (Z (t - s)) P P) ∧
      (∀ t : ℝ≥0,
        Z t =ᵐ[P] LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ)) := by
  obtain ⟨Z, hlevy, hzero, hright, hleft, hno, hmeas, hae⟩ :=
    avram_a06_original_cp_modified_levy_source P τ Y hd
  have hstrong : ∀ t : ℝ≥0, StronglyMeasurable (Z t) :=
    fun t => (hmeas t).stronglyMeasurable
  let 𝓕 := Filtration.natural (fun t => Z t) hstrong
  have hnatural := avram_e0_natural_filtration_from_leanlevy_increment
    Z hstrong hlevy.start_zero hlevy.indep_increments
  refine ⟨𝓕, Z, hzero, hright, hleft, hno, ?_, ?_, ?_, hae⟩
  · exact hnatural.1.adapted
  · intro s t hst
    exact hnatural.2 s t hst
  · intro s t hst
    have hdist := hlevy.stationary_increments s (t - s)
    have hadd : s + (t - s) = t := add_tsub_cancel_of_le hst
    rw [hadd] at hdist
    change IdentDistrib
      (fun ω => Z t ω - Z s ω)
      (fun ω => Z (t - s) ω - Z 0 ω) P P at hdist
    simpa only [hlevy.start_zero, sub_zero] using hdist
