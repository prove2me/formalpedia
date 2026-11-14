-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_uniform_gaussian_limit_original_past_independent_rep_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:41:27.478282+00:00
-- url     : https://prove2.me/submissions/108dbe74-469e-44e7-af50-5d6d64707935

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_uniform_gaussian_limit_future_borel_20261113
import Theorems.Thm_AvramDividend_Classical_avram_ja18h_original_future_path_indep_rightcont
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- One coherent source representation of Gaussian increments is measurable and independent at every start. -/
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
    (T : ℝ≥0) :
    ∃ D : ℝ≥0 → Ω → ℝ,
      (∀ s, Measurable (D s)) ∧
      (∀ s, ProbabilityTheory.Indep
        (MeasurableSpace.comap (D s) inferInstance)
        (𝓕.rightCont s) P) ∧
      (∀ᵐ ω ∂P, ∀ s : ℝ≥0,
        D s ω = R (s + T) ω - R s ω) := by
  obtain ⟨W, hW, hSource⟩ :=
    avram_a24_uniform_gaussian_limit_future_borel_20261113
      X hX hFinite R hR T
  let Shift (s : ℝ≥0) : Ω → (ℝ≥0 → ℝ) := fun ω u =>
    X.X (s + u) ω - X.X s ω
  let D : ℝ≥0 → Ω → ℝ := fun s ω => W (Shift s ω)
  have hShift (s : ℝ≥0) : Measurable (Shift s) := by
    rw [measurable_pi_iff]
    intro u
    have ht := (X.adapted (s + u)).mono (𝓕.le (s + u)) le_rfl
    have hs := (X.adapted s).mono (𝓕.le s) le_rfl
    exact ht.sub hs
  have hD (s : ℝ≥0) : Measurable (D s) := hW.comp (hShift s)
  have hIndep (s : ℝ≥0) : Indep
      (MeasurableSpace.comap (D s) inferInstance) (𝓕.rightCont s) P := by
    have hFactor : Measurable[MeasurableSpace.comap (Shift s) inferInstance]
        (D s) := by
      exact hW.comp (measurable_iff_comap_le.mpr le_rfl)
    have hPast : Indep (𝓕.rightCont s)
        (MeasurableSpace.comap (D s) inferInstance) P :=
      indep_of_indep_of_le_right
        (avram_ja18h_original_future_path_indep_rightcont X s)
        hFactor.comap_le
    exact hPast.symm
  exact ⟨D, hD, hIndep, hSource⟩
