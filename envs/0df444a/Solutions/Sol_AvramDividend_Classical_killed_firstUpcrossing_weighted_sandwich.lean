-- Prove2me | solution 1 for AvramDividend.Classical.killed_firstUpcrossing_weighted_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T13:37:58.470986+00:00
-- url     : https://prove2.me/submissions/a21fba2c-4d4f-4f83-a8b3-7db58a2adf12

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_killed_firstUpcrossing_weighted_reward_eq_survival
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_weighted_survival_lintegral_sandwich
import Theorems.Thm_AvramDividend_Classical_reflectedSup_right_continuous
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (u : Ω → ℝ≥0) (G : Set Ω)
    (hu : ∀ ω ∈ G, (u ω : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)))
    (w : Ω → ℝ≥0∞) :
    ((∫⁻ ω, if ω ∈ G ∧
       (∀ t : ℝ≥0, t < u ω → b - a ≤ X.X t ω)
       then w ω else 0 ∂P) ≤
     (∫⁻ ω, if ω ∈ G ∧
       (u ω : ℝ≥0∞) < barrierRuinTime X a ω
       then w ω else 0 ∂P)) ∧
    ((∫⁻ ω, if ω ∈ G ∧
       (u ω : ℝ≥0∞) < barrierRuinTime X a ω
       then w ω else 0 ∂P) ≤
     (∫⁻ ω, if ω ∈ G ∧
       (∀ t : ℝ≥0, t < u ω → -a ≤ X.X t ω)
       then w ω else 0 ∂P)) := by
  obtain ⟨hLo, hHi⟩ :=
    firstUpcrossing_weighted_survival_lintegral_sandwich
      X a b u G hu w
  have hRight : ∀ ω ∈ G, ContinuousWithinAt
      (fun t => reflectedSup X t ω) (Set.Ici (u ω)) (u ω) := by
    intro ω hG
    exact reflectedSup_right_continuous X ω (u ω)
  have hKilled :=
    killed_firstUpcrossing_weighted_reward_eq_survival
      X a b ha hb u G hu hRight w
  constructor
  · calc
      (∫⁻ ω, if ω ∈ G ∧
         (∀ t : ℝ≥0, t < u ω → b - a ≤ X.X t ω)
         then w ω else 0 ∂P) ≤
        (∫⁻ ω, if ω ∈ G ∧
         (∀ t : ℝ≥0, t < u ω →
           reflectedSup X t ω ≤ a)
         then w ω else 0 ∂P) := hLo
      _ = (∫⁻ ω, if ω ∈ G ∧
           (u ω : ℝ≥0∞) < barrierRuinTime X a ω
           then w ω else 0 ∂P) := hKilled.symm
  · calc
      (∫⁻ ω, if ω ∈ G ∧
         (u ω : ℝ≥0∞) < barrierRuinTime X a ω
         then w ω else 0 ∂P) =
        (∫⁻ ω, if ω ∈ G ∧
         (∀ t : ℝ≥0, t < u ω →
           reflectedSup X t ω ≤ a)
         then w ω else 0 ∂P) := hKilled
      _ ≤ (∫⁻ ω, if ω ∈ G ∧
          (∀ t : ℝ≥0, t < u ω → -a ≤ X.X t ω)
          then w ω else 0 ∂P) := hHi
