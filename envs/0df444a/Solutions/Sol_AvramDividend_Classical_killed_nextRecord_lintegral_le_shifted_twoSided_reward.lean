-- Prove2me | solution 1 for AvramDividend.Classical.killed_nextRecord_lintegral_le_shifted_twoSided_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:31:16.074995+00:00
-- url     : https://prove2.me/submissions/8bf20694-e06a-437c-86f5-cc7c85da0b64

import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_discount_global_shifted_twoSided_upper
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-! Expected killed-record domination from its already verified pointwise counterpart. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (ρ σ : Ω → ℝ≥0∞)
    (hρ : ∀ ω : Ω,
      ρ ω = (⨅ (t : ℝ≥0)
        (_ : ε < X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω -
            X.X (twoSidedExitUpTime X b ω).toNNReal ω),
        (t : ℝ≥0∞)))
    (hσ : ∀ ω : Ω,
      σ ω = (⨅ (t : ℝ≥0)
        (_ : X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω -
            X.X (twoSidedExitUpTime X b ω).toNNReal ω < -a),
        (t : ℝ≥0∞))) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
        ENNReal.ofReal ε *
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0 ∂P) ≤
    (∫⁻ ω,
      ENNReal.ofReal ε *
        (ENNReal.ofReal (Real.exp (-(q *
          ((twoSidedExitUpTime X b ω).toNNReal : ℝ)))) *
          (if ρ ω < σ ω then
            ENNReal.ofReal (Real.exp (-(q * (ρ ω).toReal)))
          else 0)) ∂P) := by
  apply lintegral_mono
  intro ω
  exact killed_nextRecord_discount_global_shifted_twoSided_upper
    X ω a b ε q ha hb hε (ρ ω) (σ ω) (hρ ω) (hσ ω)
