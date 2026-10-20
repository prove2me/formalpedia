-- Prove2me | solution 1 for AvramDividend.Classical.killed_firstUpcrossing_weighted_reward_eq_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T13:18:21.436983+00:00
-- url     : https://prove2.me/submissions/b22f6410-db8b-4021-a4b7-4effc8fab2b7

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_pre_ruin_strict_of_right_continuous
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

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
    (hRight : ∀ ω ∈ G, ContinuousWithinAt
      (fun t => reflectedSup X t ω) (Set.Ici (u ω)) (u ω))
    (w : Ω → ℝ≥0∞) :
    (∫⁻ ω, if ω ∈ G ∧
      (u ω : ℝ≥0∞) < barrierRuinTime X a ω
      then w ω else 0 ∂P) =
    (∫⁻ ω, if ω ∈ G ∧
      (∀ t : ℝ≥0, t < u ω → reflectedSup X t ω ≤ a)
      then w ω else 0 ∂P) := by
  classical
  apply lintegral_congr
  intro ω
  by_cases hG : ω ∈ G
  · have hiff :
        ((u ω : ℝ≥0∞) < barrierRuinTime X a ω) ↔
        (∀ t : ℝ≥0, t < u ω → reflectedSup X t ω ≤ a) := by
      constructor
      · intro h t ht
        apply le_of_not_gt
        intro hbad
        have hInf : barrierRuinTime X a ω ≤ (t : ℝ≥0∞) := by
          change (⨅ (s : ℝ≥0) (_ : a < drawdown X s ω),
            (s : ℝ≥0∞)) ≤ (t : ℝ≥0∞)
          have hAt : (⨅ (_ : a < drawdown X t ω),
              (t : ℝ≥0∞)) ≤ (t : ℝ≥0∞) := by
            exact iInf_le
              (fun (_ : a < drawdown X t ω) => (t : ℝ≥0∞)) hbad
          have hOuter :
              (⨅ (s : ℝ≥0) (_ : a < drawdown X s ω),
                (s : ℝ≥0∞)) ≤
              (⨅ (_ : a < drawdown X t ω), (t : ℝ≥0∞)) := by
            exact iInf_le
              (fun s : ℝ≥0 => ⨅ (_ : a < drawdown X s ω),
                (s : ℝ≥0∞)) t
          exact hOuter.trans hAt
        exact (not_lt_of_ge hInf) ((ENNReal.coe_lt_coe.mpr ht).trans h)
      · intro h
        exact firstUpcrossing_pre_ruin_strict_of_right_continuous
          X a b ha hb ω (u ω) (hu ω hG) h (hRight ω hG)
    by_cases hKilled : (u ω : ℝ≥0∞) < barrierRuinTime X a ω
    · have hSurvive := hiff.mp hKilled
      have hcL : ω ∈ G ∧
          (u ω : ℝ≥0∞) < barrierRuinTime X a ω :=
        ⟨hG, hKilled⟩
      have hcR : ω ∈ G ∧
          (∀ t : ℝ≥0, t < u ω → reflectedSup X t ω ≤ a) :=
        ⟨hG, hSurvive⟩
      simp only [if_pos hcL, if_pos hcR]
    · have hNot : ¬ (∀ t : ℝ≥0, t < u ω →
        reflectedSup X t ω ≤ a) :=
        fun hs => hKilled (hiff.mpr hs)
      have hcL : ¬ (ω ∈ G ∧
          (u ω : ℝ≥0∞) < barrierRuinTime X a ω) :=
        fun hs => hKilled hs.2
      have hcR : ¬ (ω ∈ G ∧
          (∀ t : ℝ≥0, t < u ω → reflectedSup X t ω ≤ a)) :=
        fun hs => hNot hs.2
      simp only [if_neg hcL, if_neg hcR]
  · have hcL : ¬ (ω ∈ G ∧
        (u ω : ℝ≥0∞) < barrierRuinTime X a ω) :=
      fun hs => hG hs.1
    have hcR : ¬ (ω ∈ G ∧
        (∀ t : ℝ≥0, t < u ω → reflectedSup X t ω ≤ a)) :=
      fun hs => hG hs.1
    simp only [if_neg hcL, if_neg hcR]
