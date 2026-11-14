-- Prove2me | solution 1 for AvramDividend.Classical.avram_a23_every_cutoff_increment_indep_original_past_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:14:22.497621+00:00
-- url     : https://prove2.me/submissions/055a737f-4ced-4121-b3c1-580d4148e29c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
import Theorems.Thm_AvramDividend_Classical_avram_ja18h_original_future_path_indep_rightcont
import Theorems.Thm_AvramDividend_Classical_avram_a23_every_cutoff_increment_shift_borel_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Every original finite Gaussian residual cutoff increment is independent of the actual right-continuous past. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (s t : ℝ≥0), s ≤ t →
      let D : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω
      (MeasurableSpace.comap D inferInstance ≤ mΩ) ∧
      StronglyMeasurable[MeasurableSpace.comap D inferInstance] D ∧
      ProbabilityTheory.Indep
        (MeasurableSpace.comap D inferInstance) (𝓕.rightCont s) P := by
  intro n s t hst
  let D : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
      avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω
  let Shift : Ω → (ℝ≥0 → ℝ) := fun ω u =>
    X.X (s + u) ω - X.X s ω
  obtain ⟨W, hW, hFactor⟩ :=
    avram_a23_every_cutoff_increment_shift_borel_20261113
      X hX hFinite n s t hst
  have hEq : D = W ∘ Shift := by
    funext ω
    exact hFactor ω
  have hMeas : Measurable D := by
    have ht := (avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X n t).mono (𝓕.le t) le_rfl
    have hs := (avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X n s).mono (𝓕.le s) le_rfl
    exact ht.sub hs
  have hFactorMeas : Measurable[MeasurableSpace.comap Shift inferInstance] D := by
    rw [hEq]
    exact hW.comp (measurable_iff_comap_le.mpr le_rfl)
  have hShiftIndep := avram_ja18h_original_future_path_indep_rightcont X s
  have hPast : Indep (𝓕.rightCont s)
      (MeasurableSpace.comap D inferInstance) P :=
    indep_of_indep_of_le_right hShiftIndep hFactorMeas.comap_le
  exact ⟨hMeas.comap_le,
    (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable, hPast.symm⟩
