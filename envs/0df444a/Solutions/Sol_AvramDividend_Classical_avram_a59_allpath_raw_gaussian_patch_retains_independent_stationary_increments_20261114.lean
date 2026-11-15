-- Prove2me | solution 1 for AvramDividend.Classical.avram_a59_allpath_raw_gaussian_patch_retains_independent_stationary_increments_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:26:08.388487+00:00
-- url     : https://prove2.me/submissions/ca5611db-510c-44d8-a899-0c499a96dea8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a53_raw_f0_conull_regularisation_preserves_adaptedness_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a57_raw_sigma_independence_preserved_by_conull_source_equality_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a58_original_stationary_identdistrib_preserved_conull_paths_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (G : ℝ≥0 → Ω → ℝ)
    (hAdapt : ∀ t, Measurable[𝓕 t] (G t))
    (hZero : ∀ ω, G 0 ω = 0)
    (E : Set Ω)
    (hE : MeasurableSet[𝓕 0] E)
    (hAE : ∀ᵐ ω ∂P, ω ∈ E)
    (hGood : ∀ ω ∈ E, Continuous (fun t : ℝ≥0 => G t ω))
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap
        (fun ω => G t ω - G s ω) inferInstance) (𝓕 s) P)
    (hStat : ∀ s t, s ≤ t →
      IdentDistrib (fun ω => G t ω - G s ω) (G (t - s)) P P) :
    ∃ H : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (H t)) ∧
      (∀ ω, H 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, H t ω = G t ω) ∧
      (∀ ω, Continuous (fun t : ℝ≥0 => H t ω)) ∧
      (∀ s t, s ≤ t →
        Indep (MeasurableSpace.comap
          (fun ω => H t ω - H s ω) inferInstance) (𝓕 s) P) ∧
      (∀ s t, s ≤ t →
        IdentDistrib (fun ω => H t ω - H s ω) (H (t - s)) P P) := by
  obtain ⟨H, hAdaptH, hZeroH, hEq, hCont⟩ :=
    avram_a53_raw_f0_conull_regularisation_preserves_adaptedness_20261114
      G hAdapt hZero E hE hAE hGood
  have hMeasH (t : ℝ≥0) : Measurable (H t) :=
    (hAdaptH t).mono (𝓕.le t) le_rfl
  have hStatH :=
    avram_a58_original_stationary_identdistrib_preserved_conull_paths_20261114
      G H (by
        filter_upwards [hEq] with ω hω
        intro t
        exact (hω t).symm) hMeasH hStat
  refine ⟨H, hAdaptH, hZeroH, hEq, hCont, ?_, hStatH⟩
  intro s t hst
  have hEqInc : (fun ω => G t ω - G s ω) =ᵐ[P]
      (fun ω => H t ω - H s ω) := by
    filter_upwards [hEq] with ω hω
    rw [hω t, hω s]
  exact avram_a57_raw_sigma_independence_preserved_by_conull_source_equality_20261114
    (𝓕 s) (fun ω => G t ω - G s ω)
    (fun ω => H t ω - H s ω) hEqInc (hInd s t hst)
