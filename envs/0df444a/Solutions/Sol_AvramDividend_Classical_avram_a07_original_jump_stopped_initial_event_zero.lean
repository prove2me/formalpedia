-- Prove2me | solution 1 for AvramDividend.Classical.avram_a07_original_jump_stopped_initial_event_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:37:48.438017+00:00
-- url     : https://prove2.me/submissions/c2a0ea17-107a-4625-b517-6a9259ad61b2

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (σ : Ω → ℝ≥0)
    (hJstopped :
      ∃ Jsmall : ℝ≥0 → Ω → ℝ,
        (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
          Tendsto
            (fun k : ℕ =>
              avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
            atTop (nhds (Jsmall t ω))) ∧
        (∀ t : ℝ≥0, Integrable (Jsmall t) P) ∧
        (∀ s t : ℝ≥0, s ≤ t →
          ∀ᵐ ω ∂P,
            condExp (𝓕.rightCont s) P (Jsmall t) ω = Jsmall s ω) ∧
        Integrable (fun ω => Jsmall (σ ω) ω) P ∧
        (∀ᵐ ω ∂P,
          condExp (𝓕.rightCont 0) P
            (fun ω => Jsmall (σ ω) ω) ω = 0)) :
    ∃ Jsmall : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (nhds (Jsmall t ω))) ∧
      Integrable (fun ω => Jsmall (σ ω) ω) P ∧
      (∀ S : Set Ω, MeasurableSet[𝓕.rightCont 0] S →
        ∫ ω in S, Jsmall (σ ω) ω ∂P = 0)  := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨Jsmall, hsource, htime, hmart, hstop, hzero⟩ := hJstopped
  refine ⟨Jsmall, hsource, hstop, ?_⟩
  intro S hS
  calc
    (∫ ω in S, Jsmall (σ ω) ω ∂P) =
        ∫ ω in S, condExp (𝓕.rightCont 0) P
          (fun ω => Jsmall (σ ω) ω) ω ∂P :=
      (setIntegral_condExp (𝓕.rightCont.le 0) hstop hS).symm
    _ = 0 := by
      have hz : ∀ᵐ ω ∂P, ω ∈ S →
          condExp (𝓕.rightCont 0) P (fun ω => Jsmall (σ ω) ω) ω = 0 := by
        filter_upwards [hzero] with ω heq hmem
        exact heq
      have h := setIntegral_congr_ae (𝓕.rightCont.le 0 _ hS) hz
      simpa using h
