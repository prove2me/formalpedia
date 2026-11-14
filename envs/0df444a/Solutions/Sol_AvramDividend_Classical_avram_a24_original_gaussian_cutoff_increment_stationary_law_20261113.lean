-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_original_gaussian_cutoff_increment_stationary_law_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:37:35.816037+00:00
-- url     : https://prove2.me/submissions/05e58f17-723a-4c7f-9b40-df605d9afff7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_uniform_every_gaussian_cutoff_future_borel_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a23_original_future_path_borel_functional_stationary_law_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A physical Gaussian residual cutoff has a measurable stationary-increment law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (T : ℝ≥0) :
    ∃ Z : Ω → ℝ,
      Measurable Z ∧
      ∀ s : ℝ≥0,
        Measure.map (fun ω =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X n (s + T) ω -
            avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω) P =
        Measure.map Z P := by
  obtain ⟨W, hW, hSource⟩ :=
    avram_a24_uniform_every_gaussian_cutoff_future_borel_20261113
      X hX hFinite n T
  let Path : Ω → (ℝ≥0 → ℝ) := fun ω u => X.X u ω
  let Z : Ω → ℝ := fun ω => W (Path ω)
  have hPath : Measurable Path := by
    rw [measurable_pi_iff]
    intro u
    exact (X.adapted u).mono (𝓕.le u) le_rfl
  refine ⟨Z, hW.comp hPath, ?_⟩
  intro s
  have hStat :=
    avram_a23_original_future_path_borel_functional_stationary_law_20261113
      X s W hW
  have hEq : (fun ω =>
      avram_p4_h_gaussian_intrinsic_truncated_residual X n (s + T) ω -
        avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω) =
      (fun ω => W (fun u : ℝ≥0 =>
        X.X (s + u) ω - X.X s ω)) := by
    funext ω
    exact hSource s ω
  change Measure.map (fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X n (s + T) ω -
      avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω) P =
    Measure.map (fun ω => W (Path ω)) P
  rw [hEq]
  exact hStat
