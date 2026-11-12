-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_modified_levy_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:57:48.032209+00:00
-- url     : https://prove2.me/submissions/f124d379-6069-4147-91ec-c9fbe5ab0be4

import Mathlib.Probability.ConditionalProbability
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_full_good_event
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_gated_levy
import Theorems.Thm_AvramDividend_Classical_avram_a06_gated_no_upward_left_jumps
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_fixedTime_measurable_public

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- Build the original-space Lévy modification from its full-measure path
event and its source-specific stationary independent increment theorem. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∃ (Z : ℝ≥0 → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ),
      IsLevyProcess Z P ∧
      (∀ ω, Z 0 ω = 0) ∧
      (∀ ω t, ContinuousWithinAt (fun s => Z s ω) (Ici t) t) ∧
      (∀ ω t, 0 < t →
        ∃ l, Tendsto (fun s => Z s ω) (nhdsWithin t (Iio t)) (nhds l)) ∧
      (∀ ω t l, 0 < t →
        Tendsto (fun s => Z s ω) (nhdsWithin t (Iio t)) (nhds l) →
        Z t ω ≤ l) ∧
      (∀ t, Measurable (Z t)) ∧
      (∀ t : ℝ≥0,
        Z t =ᵐ[P] LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ)) := by
  classical
  obtain ⟨G, hGmeas, hGae, hGzero, hGright, hGleft, hGdown⟩ :=
    avram_a06_original_compound_full_good_event P τ Y hd
  let Z : ℝ≥0 → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ :=
    fun t ω => if ω ∈ G then
      LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω else 0
  have hZlevy : IsLevyProcess Z P :=
    avram_a06_original_compound_gated_levy P τ Y hd G hGmeas hGae hGzero
  have hZzero : ∀ ω, Z 0 ω = 0 := by
    intro ω
    by_cases hw : ω ∈ G
    · simpa [Z, hw] using hGzero ω hw
    · simp [Z, hw]
  have hZright : ∀ ω t, ContinuousWithinAt (fun s => Z s ω) (Ici t) t := by
    intro ω t
    by_cases hw : ω ∈ G
    · simpa [Z, hw] using hGright ω hw t
    · simpa [Z, hw] using
        (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ≥0 => (0 : ℝ)) (Ici t) t)
  have hZleft : ∀ ω t, 0 < t →
      ∃ l, Tendsto (fun s => Z s ω) (nhdsWithin t (Iio t)) (nhds l) := by
    intro ω t ht
    by_cases hw : ω ∈ G
    · simpa [Z, hw] using hGleft ω hw t ht
    · refine ⟨0, ?_⟩
      simpa [Z, hw] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => (0 : ℝ)) (nhdsWithin t (Iio t)) (nhds 0))
  have hZdown : ∀ ω t l, 0 < t →
      Tendsto (fun s => Z s ω) (nhdsWithin t (Iio t)) (nhds l) → Z t ω ≤ l := by
    simpa [Z] using
      (avram_a06_gated_no_upward_left_jumps
        (fun (t : ℝ≥0) ω =>
          LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω)
        G hGdown)
  have hZm : ∀ t, Measurable (Z t) := by
    intro t
    have hraw := avram_a06_compoundPoisson_fixedTime_measurable_public
      (1 : ℝ) τ Y hd.measurable_interarrival hd.measurable_mark (t : ℝ)
    change Measurable (fun ω => if ω ∈ G then
      LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω else (0 : ℝ))
    exact Measurable.ite hGmeas hraw measurable_const
  have hZae : ∀ t : ℝ≥0,
      Z t =ᵐ[P] LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) := by
    intro t
    filter_upwards [hGae] with ω hw
    simp [Z, hw]
  exact ⟨Z, hZlevy, hZzero, hZright, hZleft, hZdown, hZm, hZae⟩
