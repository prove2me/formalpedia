-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_uncapped_nextRecord_trueFactor_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:57:12.512989+00:00
-- url     : https://prove2.me/submissions/fdbafa86-604a-4235-b4cd-35de71c6c1bd

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_nextRecord_trueFactor_lower
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_integral_eq_natTruncation
import Theorems.Thm_AvramDividend_Classical_killed_weight_global_factor_lintegral_le_of_caps
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_discount_reward_measurable
import Theorems.Thm_AvramDividend_Classical_upperPassage_measurable_from_stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The exact first-record lower renewal factor passes from every finite cap to the full killed reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    :
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
                   (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
       ENNReal.ofReal (Real.exp (-(q *
         ENNReal.toReal (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) *
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
       ENNReal.ofReal (ε * Real.exp
         (-(q * (twoSidedExitUpTime X b ω).toReal)))
      else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
       ENNReal.ofReal (ε * Real.exp
         (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0 ∂P) := by
  let reward : Ω → ℝ≥0∞ := fun ω =>
    if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp
        (-(q * (twoSidedExitUpTime X b ω).toReal)))
    else 0
  let factor : ℝ≥0∞ :=
    ∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
                   (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
       ENNReal.ofReal (Real.exp (-(q *
         ENNReal.toReal (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P
  let bound : ℝ≥0∞ :=
    ∫⁻ ω, if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp
        (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
    else 0 ∂P
  have hw : Measurable reward :=
    killed_firstRecord_discount_reward_measurable X a b ε q
  have hz : ∀ ω, twoSidedExitUpTime X b ω = ⊤ → reward ω = 0 := by
    intro ω hω
    simp [reward, hω]
  have hc (n : ℕ) :
      factor *
        (∫⁻ ω, if twoSidedExitUpTime X b ω ≤ (n : ℝ≥0∞) then
          reward ω else 0 ∂P) ≤ bound := by
    have hfin := firstRecord_capped_nextRecord_trueFactor_lower
      X a b ε q ha hb hε (n : ℝ≥0)
    rw [firstRecord_capped_integral_eq_natTruncation
      X a b ε q hε (n : ℝ≥0)] at hfin
    have hcast : ((n : ℝ≥0) : ℝ≥0∞) = (n : ℝ≥0∞) :=
      ENNReal.coe_natCast n
    have hcap :
        (∫⁻ ω, if twoSidedExitUpTime X b ω ≤ ((n : ℝ≥0) : ℝ≥0∞) then
          reward ω else 0 ∂P) =
        (∫⁻ ω, if twoSidedExitUpTime X b ω ≤ (n : ℝ≥0∞) then
          reward ω else 0 ∂P) := by
      refine lintegral_congr ?_
      intro ω
      by_cases ht : twoSidedExitUpTime X b ω ≤ (n : ℝ≥0∞)
      · simp [hcast, ht]
      · simp [hcast, ht]
    rw [hcap] at hfin
    simpa only [reward, factor, bound, mul_comm] using hfin
  have hT : Measurable (twoSidedExitUpTime X b) :=
    upperPassage_measurable_from_stopping X b
  have hglob := killed_weight_global_factor_lintegral_le_of_caps
    P (twoSidedExitUpTime X b) hT reward hw hz factor bound hc
  exact hglob
