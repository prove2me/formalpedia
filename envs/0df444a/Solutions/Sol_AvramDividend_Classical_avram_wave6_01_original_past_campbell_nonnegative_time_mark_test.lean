-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_past_campbell_nonnegative_time_mark_test
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:21:27.616205+00:00
-- url     : https://prove2.me/submissions/68179511-3ebf-4942-8b53-c5db1903c39e

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
    (s : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (f : (ℝ≥0 × ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∃ Q : Measure (ℝ≥0 × ℝ),
      (∀ C : Set (ℝ≥0 × ℝ), MeasurableSet C →
        Q C = (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) C ∂P)) ∧
      (∫⁻ p, f p ∂Q) =
        (∫⁻ ω in A, (∫⁻ p, f p ∂
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P) := by
  classical
  obtain ⟨κ, hκFinite, hκ⟩ :=
    avram_wave5_02a_actual_source_intrinsic_sfinite_kernel X
  let Q : Measure (ℝ≥0 × ℝ) := (P.restrict A).bind κ
  refine ⟨Q, ?_, ?_⟩
  · intro C hC
    calc
      Q C = ∫⁻ ω, κ ω C ∂(P.restrict A) := by
        exact Measure.bind_apply hC
          (ProbabilityTheory.Kernel.measurable κ).aemeasurable
      _ = (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) C ∂P) := by
        change (∫⁻ ω in A, κ ω C ∂P) =
          (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) C ∂P)
        apply lintegral_congr
        intro ω
        exact congrArg
          (fun μ : Measure (ℝ≥0 × ℝ) => μ C) (hκ ω)
  · calc
      (∫⁻ p, f p ∂Q) =
        (∫⁻ ω in A, (∫⁻ p, f p ∂(κ ω)) ∂P) := by
          exact Measure.lintegral_bind
            (ProbabilityTheory.Kernel.measurable κ).aemeasurable
            hf.aemeasurable
      _ = (∫⁻ ω in A, (∫⁻ p, f p ∂
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P) := by
          apply lintegral_congr
          intro ω
          exact congrArg
            (fun μ : Measure (ℝ≥0 × ℝ) =>
              ∫⁻ p, f p ∂μ) (hκ ω)
