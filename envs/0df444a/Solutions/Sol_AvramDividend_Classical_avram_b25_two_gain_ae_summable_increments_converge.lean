-- Prove2me | solution 1 for AvramDividend.Classical.avram_b25_two_gain_ae_summable_increments_converge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T01:01:44.342205+00:00
-- url     : https://prove2.me/submissions/bff3f53e-58f3-4ebe-b2ab-7a0df959b6dd

import Mathlib
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (G J : ℕ → Ω → ℝ)
    (hGa : ∀ᵐ ω ∂P, Summable
      (fun k : ℕ => ‖G (k + 1) ω - G k ω‖))
    (hJa : ∀ᵐ ω ∂P, Summable
      (fun k : ℕ => ‖J (k + 1) ω - J k ω‖)) :
    ∃ (MG MJ : Ω → ℝ),
      (∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (MG ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => J k ω) atTop (𝓝 (MJ ω))) := by
  classical
  refine ⟨(fun ω => Filter.atTop.limUnder (fun k => G k ω)),
    (fun ω => Filter.atTop.limUnder (fun k => J k ω)), ?_, ?_⟩
  · filter_upwards [hGa] with ω hω
    have hDist : Summable (fun k : ℕ => dist (G k ω) (G (k + 1) ω)) := by
      simpa only [dist_eq_norm, norm_sub_rev] using hω
    exact (cauchySeq_of_summable_dist hDist).tendsto_limUnder
  · filter_upwards [hJa] with ω hω
    have hDist : Summable (fun k : ℕ => dist (J k ω) (J (k + 1) ω)) := by
      simpa only [dist_eq_norm, norm_sub_rev] using hω
    exact (cauchySeq_of_summable_dist hDist).tendsto_limUnder
