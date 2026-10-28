-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_capped_trueTwoSided_expected_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T00:15:59.631892+00:00
-- url     : https://prove2.me/submissions/e3c550ac-337d-4e8b-b639-28d6a08be987

import Theorems.Thm_AvramDividend_Classical_finiteStopping_trueTwoSided_expected_upper_of_pointwise_preamble_fixed
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_in_finiteStoppedHistory
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) (N : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : τ = (fun ω : Ω =>
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal))
    (A : Set Ω)
    (hA : A = ({ω : Ω | twoSidedExitUpTime X b ω <
      barrierRuinTime X a ω} ∩
      {ω : Ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}))
    (hAfine : MeasurableSet A)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (q upper lower : ℝ) (weight : Ω → ℝ≥0∞)
    (hUpper : ∀ ω : Ω, weight ω ≤
      (if ω ∈ A then discount (τ ω) *
        (let g : ℝ≥0 → ℝ := fun t => X.X (τ ω + t) ω - X.X (τ ω) ω
         let grid : ℕ → ℝ≥0 := fun j => ((Nat.unpair j).2 : ℝ≥0) *
           (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
         let up : ℝ≥0∞ := ⨅ j : ℕ,
           if upper < g (grid j) then (grid j : ℝ≥0∞) else ⊤
         let dn : ℝ≥0∞ := ⨅ j : ℕ,
           if g (grid j) < lower then (grid j : ℝ≥0∞) else ⊤
         if up < dn then ENNReal.ofReal (Real.exp (-(q * up.toReal))) else 0)
       else 0)) :
    (∫⁻ ω, weight ω ∂P) ≤
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : upper < X.X t ω),
                    (t : ℝ≥0∞)) <
                  (⨅ (t : ℝ≥0) (_ : X.X t ω < lower),
                    (t : ℝ≥0∞)) then
      ENNReal.ofReal (Real.exp (-(q *
        ENNReal.toReal (⨅ (t : ℝ≥0)
          (_ : upper < X.X t ω), (t : ℝ≥0∞))))) else 0 ∂P) := by
  subst τ
  subst A
  exact finiteStopping_trueTwoSided_expected_upper_of_pointwise_preamble_fixed
    X
    (fun ω : Ω =>
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal)
    (firstRecord_truncation_stopping_rightCont X b N)
    ({ω : Ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω} ∩
      {ω : Ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)})
    (firstRecord_capped_survival_in_finiteStoppedHistory X a b N)
    hAfine
    (firstRecord_truncation_clock_measurable X b N)
    discount hd q upper lower weight hUpper