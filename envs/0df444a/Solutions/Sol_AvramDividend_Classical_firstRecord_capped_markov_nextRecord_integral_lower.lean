-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_capped_markov_nextRecord_integral_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:36:23.530793+00:00
-- url     : https://prove2.me/submissions/24c02d62-4a55-49f8-8057-f14fe8d16e54

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_namedShiftedReward_markov_lower
import Theorems.Thm_AvramDividend_Classical_capped_trueShiftedReward_expected_le_nextRecord
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

/-- The capped first-record strong-Markov inequality controls the next killed record. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (N : ℝ≥0)
    (hd : Measurable (fun t : ℝ≥0 =>
      ENNReal.ofReal ε * ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))))) :
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
         twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
       ENNReal.ofReal ε *
         ENNReal.ofReal (Real.exp (-(q *
           (((min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal) : ℝ))))
      else 0 ∂P) *
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
                   (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
       ENNReal.ofReal (Real.exp (-(q *
         ENNReal.toReal (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
       ENNReal.ofReal (ε * Real.exp
         (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0 ∂P) := by
  let τ : Ω → ℝ≥0 :=
    fun ω => (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
  let discount : ℝ≥0 → ℝ≥0∞ :=
    fun t => ENNReal.ofReal ε * ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
  let ρ : Ω → ℝ≥0∞ := fun ω =>
    ⨅ i : {t : ℝ≥0 // ε < X.X (τ ω + t) ω - X.X (τ ω) ω},
      (i.1 : ℝ≥0∞)
  let σ : Ω → ℝ≥0∞ := fun ω =>
    ⨅ i : {t : ℝ≥0 // X.X (τ ω + t) ω - X.X (τ ω) ω < ε - a},
      (i.1 : ℝ≥0∞)
  have hd' : Measurable discount := hd
  have hm := firstRecord_capped_namedShiftedReward_markov_lower
    X a b N τ rfl discount hd' q ε (ε - a) ρ σ
    (fun _ => rfl) (fun _ => rfl)
  have ht := capped_trueShiftedReward_expected_le_nextRecord
    X a b ε q ha hb hε N
  have hcomp :
      (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
          twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
        discount (τ ω) *
          (if ρ ω < σ ω then ENNReal.ofReal (Real.exp (-(q * (ρ ω).toReal)))
           else 0)
        else 0 ∂P) ≤
      (∫⁻ ω, if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
         ENNReal.ofReal (ε * Real.exp
           (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
       else 0 ∂P) := by
    simpa only [τ, discount, ρ, σ, mul_assoc] using ht
  simpa only [τ, discount] using hm.trans hcomp
