-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_event_weighted_marked_count_is_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:16:14.084606+00:00
-- url     : https://prove2.me/submissions/36fdf951-d72c-4f2e-ad7d-7253c51f7395

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
    (A : Set Ω) (hA : MeasurableSet A) :
    ∃ M : Measure (ℝ≥0 × ℝ),
      ∀ C : Set (ℝ≥0 × ℝ), MeasurableSet C →
        M C = (∫⁻ ω in A,
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u))) C ∂P) := by
  classical
  obtain ⟨κ, hκSFinite, hκ⟩ :=
    avram_wave5_02a_actual_source_intrinsic_sfinite_kernel X
  let M : Measure (ℝ≥0 × ℝ) :=
    (P.restrict A).bind (fun ω => κ ω)
  refine ⟨M, ?_⟩
  intro C hC
  have hm : AEMeasurable
      (fun ω => (κ ω : Measure (ℝ≥0 × ℝ))) (P.restrict A) :=
    (Kernel.measurable κ).aemeasurable
  change M C =
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u))) C ∂P)
  rw [show M C = (∫⁻ ω in A, κ ω C ∂P) from
    Measure.bind_apply hC hm]
  simp_rw [hκ]
