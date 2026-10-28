-- Prove2me | solution 1 for AvramDividend.Classical.killed_nextRecord_capped_pathwise_shifted_upper
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:09:50.060476+00:00
-- url     : https://prove2.me/submissions/408654f4-ebd5-4097-b020-314eb132d002

import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_discount_global_shifted_twoSided_upper
import Theorems.Thm_AvramDividend_Classical_killed_higherRecord_survival_implies_lowerRecord_survival_with_measure_import
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (N : ℝ≥0) (ρ σ : ℝ≥0∞)
    (hρ : ρ = (⨅ (t : ℝ≥0)
      (_ : ε < X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω -
          X.X (twoSidedExitUpTime X b ω).toNNReal ω), (t : ℝ≥0∞)))
    (hσ : σ = (⨅ (t : ℝ≥0)
      (_ : X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω -
          X.X (twoSidedExitUpTime X b ω).toNNReal ω < -a), (t : ℝ≥0∞))) :
    (if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X (b + ε) ω ≤ (N : ℝ≥0∞) then
      ENNReal.ofReal ε *
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0) ≤
    (if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      ENNReal.ofReal ε *
        (ENNReal.ofReal (Real.exp (-(q *
          ((twoSidedExitUpTime X b ω).toNNReal : ℝ)))) *
          (if ρ < σ then
            ENNReal.ofReal (Real.exp (-(q * ρ.toReal)))
          else 0))
      else 0) := by 
  by_cases h : twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω ∧
      twoSidedExitUpTime X (b + ε) ω ≤ (N : ℝ≥0∞)
  · have hlow := killed_higherRecord_survival_implies_lowerRecord_survival_with_measure_import
      X a b ε hε ω h.1
    have hN : twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) :=
      (twoSidedExitUpTime_mono_threshold X b (b + ε) (by linarith) ω).trans h.2
    rw [if_pos h, if_pos ⟨hlow, hN⟩]
    have := killed_nextRecord_discount_global_shifted_twoSided_upper X ω a b ε q ha hb hε ρ σ hρ hσ
    rwa [if_pos h.1] at this
  · rw [if_neg h]; exact zero_le
