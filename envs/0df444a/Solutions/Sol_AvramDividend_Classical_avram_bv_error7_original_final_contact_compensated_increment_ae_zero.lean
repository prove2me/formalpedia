-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_final_contact_compensated_increment_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:23:59.349731+00:00
-- url     : https://prove2.me/submissions/b881b37a-3f42-4179-b6d5-0ba8ce73ce24

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The unique last physical cell has vanishing compensated BV increment,
including paths whose stopped index is zero. No value-function C1 condition
is imposed on this final ruin/horizon contact cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (hMesh : ∀ᵐ ω ∂P,
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       ∀ δ : ℝ, 0 < δ → ∀ᶠ m in Filter.atTop,
         ∀ i, i < k m ω →
           |Y (u m (i + 1)) - Y (u m i)| < δ)) :
    ∀ᵐ ω ∂P,
      Tendsto (fun m =>
        let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
          else 0
        let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
        if k m ω = 0 then (0 : ℝ)
        else Y (u m (k m ω)) - Y (u m (k m ω - 1)))
        atTop (nhds (0 : ℝ)) := by
  filter_upwards [hMesh] with ω hω
  dsimp at hω ⊢
  apply (Metric.tendsto_atTop).2
  intro δ hδ
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hω δ hδ)
  refine ⟨N, ?_⟩
  intro m hm
  by_cases hk : k m ω = 0
  · simp [hk, Real.dist_eq, hδ]
  · have hlt : k m ω - 1 < k m ω := by omega
    have hNext : k m ω - 1 + 1 = k m ω := by omega
    have hSmall := hN m hm (k m ω - 1) hlt
    simpa [hk, hNext, Real.dist_eq, sub_zero] using hSmall
