-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_signed_spatial_K_mask_preserves_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:57:46.680115+00:00
-- url     : https://prove2.me/submissions/9c85f8f6-2222-401a-baeb-d88282b119b3

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : Set Ω) (hS : MeasurableSet S)
    (K : Ω → ℝ) (hKI : Integrable K P)
    (ε : ℝ) (hKsmall : (∫ ω, |K ω| ∂P) ≤ ε) :
    ∃ K' : Ω → ℝ,
      Integrable K' P ∧
      (∫ ω, |K' ω| ∂P) ≤ ε ∧
      (∀ ω, ω ∉ S → K' ω = 0) ∧
      (∀ ω, ω ∈ S → K' ω = K ω) := by 
  let K' : Ω → ℝ := S.indicator K
  have hK'I : Integrable K' P := hKI.indicator hS
  have hAbs : (fun ω => |K' ω|) = S.indicator (fun ω => |K ω|) := by
    funext ω
    by_cases hs : ω ∈ S
    · simp [K', Set.indicator_of_mem hs]
    · simp [K', Set.indicator_of_notMem hs]
  have hBound : (∫ ω, |K' ω| ∂P) ≤ ∫ ω, |K ω| ∂P := by
    rw [hAbs]
    apply integral_mono_ae (hKI.abs.indicator hS) hKI.abs
    filter_upwards [] with ω
    by_cases hs : ω ∈ S
    · rw [Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs]
      exact abs_nonneg _
  refine ⟨K', hK'I, hBound.trans hKsmall, ?_, ?_⟩
  · intro ω hω
    simp [K', Set.indicator_of_notMem hω]
  · intro ω hω
    simp [K', Set.indicator_of_mem hω]
