-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_bounded_original_Borel_mark_simple_quantization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T20:50:15.713959+00:00
-- url     : https://prove2.me/submissions/2bea5f88-13a3-4754-88a0-9ae51ad79962

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped Topology
noncomputable section
theorem solution
    (g : ℝ → ℝ) (S : Set ℝ)
    (hg : Measurable g) (hS : MeasurableSet S)
    (hBound : ∀ z ∈ S, ‖g z‖ ≤ 1) :
    ∃ f : ℕ → SimpleFunc ℝ ℝ,
      (∀ k z, ‖f k z‖ ≤ 1) ∧
      (∀ z ∈ S, Tendsto (fun k => f k z) atTop (𝓝 (g z))) := by
  classical
  have hMeas : StronglyMeasurable (S.indicator g) :=
    hg.stronglyMeasurable.indicator hS
  refine ⟨fun k => hMeas.approxBounded 1 k, ?_, ?_⟩
  · intro k z
    exact hMeas.norm_approxBounded_le (by norm_num) k z
  · intro z hz
    have hNorm : ‖(S.indicator g) z‖ ≤ (1 : ℝ) := by
      simpa only [Set.indicator_of_mem hz] using hBound z hz
    have hTendsto :=
      hMeas.tendsto_approxBounded_of_norm_le hNorm
    simpa only [Set.indicator_of_mem hz] using hTendsto
