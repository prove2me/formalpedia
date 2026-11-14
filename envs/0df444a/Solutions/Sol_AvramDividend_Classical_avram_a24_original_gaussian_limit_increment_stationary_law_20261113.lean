-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_original_gaussian_limit_increment_stationary_law_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:39:53.934995+00:00
-- url     : https://prove2.me/submissions/19e184ea-aaec-458f-a9ce-76fadbc3968e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_uniform_gaussian_limit_future_borel_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a23_original_future_path_borel_functional_stationary_law_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Every original Gaussian residual limit increment of fixed duration has one stationary law. -/
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
    ∃ Z : Ω → ℝ, Measurable Z ∧
      ∀ s : ℝ≥0,
        Measure.map (fun ω => R (s + T) ω - R s ω) P =
        Measure.map Z P := by
  obtain ⟨W, hW, hSource⟩ :=
    avram_a24_uniform_gaussian_limit_future_borel_20261113
      X hX hFinite R hR T
  let Path : Ω → (ℝ≥0 → ℝ) := fun ω u => X.X u ω
  let Z : Ω → ℝ := fun ω => W (Path ω)
  have hPath : Measurable Path := by
    rw [measurable_pi_iff]
    intro u
    exact (X.adapted u).mono (𝓕.le u) le_rfl
  refine ⟨Z, hW.comp hPath, ?_⟩
  intro s
  have hEq : (fun ω => R (s + T) ω - R s ω) =ᵐ[P]
      (fun ω => W (fun u : ℝ≥0 =>
        X.X (s + u) ω - X.X s ω)) := by
    filter_upwards [hSource] with ω hω
    exact (hω s).symm
  have hStat :=
    avram_a23_original_future_path_borel_functional_stationary_law_20261113
      X s W hW
  calc
    Measure.map (fun ω => R (s + T) ω - R s ω) P =
      Measure.map (fun ω => W (fun u : ℝ≥0 =>
        X.X (s + u) ω - X.X s ω)) P := Measure.map_congr hEq
    _ = Measure.map Z P := hStat
