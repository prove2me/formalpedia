-- Prove2me | solution 2 for AvramDividend.Classical.avram_a06_original_compoundPoisson_path_increment_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T22:38:47.168931+00:00
-- url     : https://prove2.me/submissions/59f4b8b8-3169-4471-b31b-9306ed74060e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_modified_levy_source
import Theorems.Thm_AvramDividend_Classical_avram_e0_natural_filtration_from_leanlevy_increment
import Theorems.Thm_ProbabilityTheory_increment_apply
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

/-- Upgrade an original zero-gated Lévy modification to its natural filtration. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
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
  obtain ⟨Z, hZlevy, hZzero, hZright, hZleft, hZdown, hZm, hZae⟩ :=
    avram_a06_original_cp_modified_levy_source P τ Y hd
  have hZsm : ∀ t : ℝ≥0, StronglyMeasurable (Z t) :=
    fun t => (hZm t).stronglyMeasurable
  have hzeroFun : Z 0 = fun _ => 0 := by
    funext ω
    exact hZzero ω
  let 𝓕 : Filtration ℝ≥0
      (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))) :=
    Filtration.natural (fun t => Z t) hZsm
  have hnat := avram_e0_natural_filtration_from_leanlevy_increment
    Z hZsm hzeroFun hZlevy.indep_increments
  have hadapted : Adapted 𝓕 Z := by
    intro t
    exact (hnat.1 t).measurable
  have hindep : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap
        (fun ω => Z t ω - Z s ω) inferInstance) (𝓕 s) P := by
    intro s t hst
    simpa [𝓕] using hnat.2 s t hst
  have hstation : ∀ s t, s ≤ t →
      IdentDistrib (fun ω => Z t ω - Z s ω) (Z (t - s)) P P := by
    intro s t hst
    have ht : s + (t - s) = t := add_tsub_cancel_of_le hst
    have hleft :
        ProbabilityTheory.increment Z s (s + (t - s)) =
          (fun ω => Z t ω - Z s ω) := by
      funext ω
      simp [ProbabilityTheory.increment_apply, ht]
    have hright :
        ProbabilityTheory.increment Z 0 (t - s) = Z (t - s) := by
      funext ω
      simp [ProbabilityTheory.increment_apply, hZzero]
    simpa only [hleft, hright] using
      (hZlevy.stationary_increments s (t - s))
  exact ⟨𝓕, Z, hZzero, hZright, hZleft, hZdown,
    hadapted, hindep, hstation, hZae⟩
