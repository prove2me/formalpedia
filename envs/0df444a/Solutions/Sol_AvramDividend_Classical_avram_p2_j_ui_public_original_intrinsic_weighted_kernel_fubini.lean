-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_public_original_intrinsic_weighted_kernel_fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:36:34.503129+00:00
-- url     : https://prove2.me/submissions/ce8d084b-968c-4177-96b0-0b033a9b0213

import Mathlib.MeasureTheory.Measure.GiryMonad
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual source time-mark expected measure satisfies weighted Fubini for all nonnegative measurable tests. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (g : (ℝ≥0 × ℝ) → ℝ≥0∞) (hg : Measurable g) :
    ∃ Q : Measure (ℝ≥0 × ℝ),
      (∀ C : Set (ℝ≥0 × ℝ), MeasurableSet C →
        Q C = (∫⁻ ω,
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            C ∂P)) ∧
      (∫⁻ p, g p ∂Q) =
        (∫⁻ ω, (∫⁻ p, g p ∂
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P) := by
  classical
  obtain ⟨κ, _, hκ⟩ :=
    avram_wave5_02a_actual_source_intrinsic_sfinite_kernel X
  let Q : Measure (ℝ≥0 × ℝ) := P.bind (fun ω => κ ω)
  have hκMeas : AEMeasurable
      (fun ω => (κ ω : Measure (ℝ≥0 × ℝ))) P :=
    (Kernel.measurable κ).aemeasurable
  refine ⟨Q, ?_, ?_⟩
  · intro C hC
    change Q C = (∫⁻ ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        C ∂P)
    rw [show Q C = (∫⁻ ω, κ ω C ∂P) from
      Measure.bind_apply hC hκMeas]
    simp_rw [hκ]
  · change (∫⁻ p, g p ∂(P.bind (fun ω => κ ω))) =
      (∫⁻ ω, (∫⁻ p, g p ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P)
    rw [Measure.lintegral_bind hκMeas hg.aemeasurable]
    simp_rw [hκ]
