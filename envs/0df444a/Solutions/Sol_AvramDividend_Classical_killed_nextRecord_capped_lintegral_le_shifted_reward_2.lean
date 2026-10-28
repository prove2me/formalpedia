-- Prove2me | solution 2 for AvramDividend.Classical.killed_nextRecord_capped_lintegral_le_shifted_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T00:15:45.033071+00:00
-- url     : https://prove2.me/submissions/20227e09-8f7e-4cb9-a9a7-532fc07f9fd3

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_capped_pathwise_shifted_upper
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (N : ℝ≥0) (ρ σ : Ω → ℝ≥0∞)
    (hρ : ∀ ω : Ω, ρ ω = (⨅ (t : ℝ≥0)
      (_ : ε < X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω -
          X.X (twoSidedExitUpTime X b ω).toNNReal ω), (t : ℝ≥0∞)))
    (hσ : ∀ ω : Ω, σ ω = (⨅ (t : ℝ≥0)
      (_ : X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω -
          X.X (twoSidedExitUpTime X b ω).toNNReal ω < -a), (t : ℝ≥0∞))) :
    (∫⁻ ω, if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X (b + ε) ω ≤ (N : ℝ≥0∞) then
      ENNReal.ofReal ε *
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      ENNReal.ofReal ε *
        (ENNReal.ofReal (Real.exp (-(q *
          ((twoSidedExitUpTime X b ω).toNNReal : ℝ)))) *
          (if ρ ω < σ ω then
            ENNReal.ofReal (Real.exp (-(q * (ρ ω).toReal)))
          else 0))
      else 0 ∂P) := by
  apply lintegral_mono
  intro ω
  exact killed_nextRecord_capped_pathwise_shifted_upper
    X ω a b ε q ha hb hε N (ρ ω) (σ ω) (hρ ω) (hσ ω)