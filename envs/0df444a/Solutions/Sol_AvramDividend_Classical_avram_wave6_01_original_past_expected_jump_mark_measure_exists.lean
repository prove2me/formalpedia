-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_past_expected_jump_mark_measure_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:00:43.362225+00:00
-- url     : https://prove2.me/submissions/1fb4f102-4d67-4e39-8591-da076c802b49

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
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    ∃ ρ : Measure ℝ, ∀ B : Set ℝ, MeasurableSet B →
      ρ B = (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) := by
  classical
  obtain ⟨κ, hκFinite, hκ⟩ :=
    avram_wave5_02a_actual_source_intrinsic_sfinite_kernel X
  let Q : Measure (ℝ≥0 × ℝ) := (P.restrict A).bind κ
  let R : Measure (ℝ≥0 × ℝ) :=
    Q.restrict (Ioc s t ×ˢ (Set.univ : Set ℝ))
  let ρ : Measure ℝ := R.map Prod.snd
  refine ⟨ρ, ?_⟩
  intro B hB
  have hSetB : MeasurableSet (Ioc s t ×ˢ B) :=
    measurableSet_Ioc.prod hB
  have hPreimage : MeasurableSet ((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) :=
    measurable_snd hB
  have hSetEq :
      ((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) ∩
          (Ioc s t ×ˢ (Set.univ : Set ℝ)) =
        Ioc s t ×ˢ B := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ,
      and_true]
    exact and_comm
  calc
    ρ B = R ((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) := by
      exact Measure.map_apply measurable_snd hB
    _ = Q (((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) ∩
          (Ioc s t ×ˢ (Set.univ : Set ℝ))) := by
      exact Measure.restrict_apply hPreimage
    _ = Q (Ioc s t ×ˢ B) := by rw [hSetEq]
    _ = ∫⁻ ω, κ ω (Ioc s t ×ˢ B) ∂(P.restrict A) := by
      exact Measure.bind_apply hSetB
        (ProbabilityTheory.Kernel.measurable κ).aemeasurable
    _ = ∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) ∂P := by
      change (∫⁻ ω in A, κ ω (Ioc s t ×ˢ B) ∂P) =
        (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) ∂P)
      apply lintegral_congr
      intro ω
      exact congrArg
        (fun μ : Measure (ℝ≥0 × ℝ) => μ (Ioc s t ×ˢ B)) (hκ ω)
