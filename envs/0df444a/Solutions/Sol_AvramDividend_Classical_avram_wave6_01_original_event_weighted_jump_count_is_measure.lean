-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_event_weighted_jump_count_is_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:54:45.471699+00:00
-- url     : https://prove2.me/submissions/76c23b34-7b3d-4e1b-aa7b-694b5f76b6e8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : Set (ℝ≥0 × ℝ)) (hC : MeasurableSet C) :
    ∃ Q : Measure Ω, ∀ A : Set Ω, MeasurableSet A →
      Q A = (∫⁻ ω in A,
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u))) C ∂P) := by
  classical
  obtain ⟨κ, hκFinite, hκ⟩ :=
    avram_wave5_02a_actual_source_intrinsic_sfinite_kernel X
  let f : Ω → ℝ≥0∞ := fun ω => κ ω C
  let Q : Measure Ω := P.withDensity f
  refine ⟨Q, ?_⟩
  intro A hA
  calc
    Q A = ∫⁻ ω in A, f ω ∂P := by
      exact withDensity_apply f hA
    _ = ∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u))) C ∂P := by
      apply lintegral_congr
      intro ω
      exact congrArg (fun μ : Measure (ℝ≥0 × ℝ) => μ C) (hκ ω)
