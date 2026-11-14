-- Prove2me | solution 1 for AvramDividend.Classical.avram_a23_gaussian_limit_increment_original_past_independent_rep_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:18:38.127602+00:00
-- url     : https://prove2.me/submissions/544901f5-9333-4f71-91ad-d8163ea7a80e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a23_gaussian_limit_increment_canonical_future_borel_20261113
import Theorems.Thm_AvramDividend_Classical_avram_ja18h_original_future_path_indep_rightcont
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original Gaussian limit increment has a measurable representative independent of the original past. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n u ω)
        atTop (𝓝 (R u ω)))
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∃ D : Ω → ℝ,
      Measurable D ∧
      ProbabilityTheory.Indep (MeasurableSpace.comap D inferInstance)
        (𝓕.rightCont s) P ∧
      (∀ᵐ ω ∂P, D ω = R t ω - R s ω) := by
  obtain ⟨W, hW, hLimit⟩ :=
    avram_a23_gaussian_limit_increment_canonical_future_borel_20261113
      X hX hFinite R hR s t hst
  let Shift : Ω → (ℝ≥0 → ℝ) := fun ω u =>
    X.X (s + u) ω - X.X s ω
  let D : Ω → ℝ := fun ω => W (Shift ω)
  have hShift : Measurable Shift := by
    rw [measurable_pi_iff]
    intro u
    have ht := (X.adapted (s + u)).mono (𝓕.le (s + u)) le_rfl
    have hs := (X.adapted s).mono (𝓕.le s) le_rfl
    exact ht.sub hs
  have hD : Measurable D := hW.comp hShift
  have hFactor : Measurable[MeasurableSpace.comap Shift inferInstance] D := by
    exact hW.comp (measurable_iff_comap_le.mpr le_rfl)
  have hPast : Indep (𝓕.rightCont s)
      (MeasurableSpace.comap D inferInstance) P :=
    indep_of_indep_of_le_right
      (avram_ja18h_original_future_path_indep_rightcont X s)
      hFactor.comap_le
  exact ⟨D, hD, hPast.symm, hLimit⟩
