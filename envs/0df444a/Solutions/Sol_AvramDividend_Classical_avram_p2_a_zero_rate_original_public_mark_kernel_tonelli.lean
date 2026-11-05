-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_public_mark_kernel_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:51:35.305544+00:00
-- url     : https://prove2.me/submissions/b1e2d4fd-ae82-4a5c-9009-749a3bf26e07

import Mathlib.MeasureTheory.Measure.GiryMonad
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
import Mathlib.Probability.Kernel.Defs
import Mathlib.Topology.Order.LeftRightLim
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Public original jump kernel and Tonelli mean-measure construction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (g : (ℝ≥0 × ℝ) → ℝ≥0∞) (hg : Measurable g) :
    ∃ M : Measure (ℝ≥0 × ℝ),
      (∀ C : Set (ℝ≥0 × ℝ), MeasurableSet C →
        M C = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) C ∂P)) ∧
      (∫⁻ p, g p ∂M) =
        (∫⁻ ω, ∫⁻ p, g p ∂
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P) := by
  obtain ⟨κ, hκfinite, hκeq⟩ :=
    avram_wave5_02a_actual_source_intrinsic_sfinite_kernel X
  have hκm : AEMeasurable (fun ω : Ω => κ ω) P :=
    (ProbabilityTheory.Kernel.measurable κ).aemeasurable
  refine ⟨P.bind (fun ω => κ ω), ?_, ?_⟩
  · intro C hC
    rw [Measure.bind_apply hC hκm]
    apply lintegral_congr_ae
    filter_upwards [] with ω
    rw [hκeq ω]
  · rw [Measure.lintegral_bind hκm hg.aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [] with ω
    rw [hκeq ω]
