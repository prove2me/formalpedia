-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_weighted_survival_lintegral_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T11:05:41.562647+00:00
-- url     : https://prove2.me/submissions/b925b521-b2ac-4efa-a08c-96e52ce73625

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_drawdown_survival_sandwich

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (u : Ω → ℝ≥0) (G : Set Ω)
    (hu : ∀ ω ∈ G, ((u ω : ℝ≥0) : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)))
    (w : Ω → ℝ≥0∞) :
    (∫⁻ ω, if ω ∈ G ∧
          (∀ t : ℝ≥0, t < u ω → b - a ≤ X.X t ω)
        then w ω else 0 ∂P) ≤
    (∫⁻ ω, if ω ∈ G ∧
          (∀ t : ℝ≥0, t < u ω →
            runningSup X t ω - X.X t ω ≤ a)
        then w ω else 0 ∂P) ∧
    (∫⁻ ω, if ω ∈ G ∧
          (∀ t : ℝ≥0, t < u ω →
            runningSup X t ω - X.X t ω ≤ a)
        then w ω else 0 ∂P) ≤
    (∫⁻ ω, if ω ∈ G ∧
          (∀ t : ℝ≥0, t < u ω → -a ≤ X.X t ω)
        then w ω else 0 ∂P) := by
  classical
  constructor
  · refine lintegral_mono (fun ω => ?_)
    by_cases hG : ω ∈ G
    · obtain ⟨hRawToDraw, _⟩ :=
        firstUpcrossing_drawdown_survival_sandwich
          X a b ω (u ω) (hu ω hG)
      by_cases hRaw :
          ∀ t : ℝ≥0, t < u ω → b - a ≤ X.X t ω
      · have hDraw := hRawToDraw hRaw
        have hCondA : ω ∈ G ∧
            (∀ t : ℝ≥0, t < u ω → b - a ≤ X.X t ω) :=
          ⟨hG, hRaw⟩
        have hCondB : ω ∈ G ∧
            (∀ t : ℝ≥0, t < u ω →
              runningSup X t ω - X.X t ω ≤ a) :=
          ⟨hG, hDraw⟩
        simpa only [if_pos hCondA, if_pos hCondB] using
          (le_refl (w ω))
      · have hn : ¬ (ω ∈ G ∧
            ∀ t : ℝ≥0, t < u ω → b - a ≤ X.X t ω) :=
          fun h => hRaw h.2
        rw [if_neg hn]
        exact bot_le
    · have hn : ¬ (ω ∈ G ∧
          ∀ t : ℝ≥0, t < u ω → b - a ≤ X.X t ω) :=
        fun h => hG h.1
      rw [if_neg hn]
      exact bot_le
  · refine lintegral_mono (fun ω => ?_)
    by_cases hG : ω ∈ G
    · obtain ⟨_, hDrawToRaw⟩ :=
        firstUpcrossing_drawdown_survival_sandwich
          X a b ω (u ω) (hu ω hG)
      by_cases hDraw :
          ∀ t : ℝ≥0, t < u ω →
            runningSup X t ω - X.X t ω ≤ a
      · have hRaw := hDrawToRaw hDraw
        have hCondA : ω ∈ G ∧
            (∀ t : ℝ≥0, t < u ω →
              runningSup X t ω - X.X t ω ≤ a) :=
          ⟨hG, hDraw⟩
        have hCondB : ω ∈ G ∧
            (∀ t : ℝ≥0, t < u ω → -a ≤ X.X t ω) :=
          ⟨hG, hRaw⟩
        simpa only [if_pos hCondA, if_pos hCondB] using
          (le_refl (w ω))
      · have hn : ¬ (ω ∈ G ∧
            ∀ t : ℝ≥0, t < u ω →
              runningSup X t ω - X.X t ω ≤ a) :=
          fun h => hDraw h.2
        rw [if_neg hn]
        exact bot_le
    · have hn : ¬ (ω ∈ G ∧
          ∀ t : ℝ≥0, t < u ω →
            runningSup X t ω - X.X t ω ≤ a) :=
        fun h => hG h.1
      rw [if_neg hn]
      exact bot_le
