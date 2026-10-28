-- Prove2me | solution 1 for AvramDividend.Classical.stopped_discounted_real_cash_prefix_measurable_of_strategy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:37:43.043205+00:00
-- url     : https://prove2.me/submissions/4f985cda-81a8-4625-bc24-e80e068cb437

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Data.Finset.Range
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_unit_cash_measurable_of_strategy
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Every finite real-cash prefix of a stopped admissible Stieltjes
    dividend strategy is a measurable ENNReal-valued random variable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (T : ℝ≥0) :
    ∀ n : ℕ, Measurable (fun ω : Ω =>
      ENNReal.ofReal
        (∑ k ∈ Finset.range n,
          (∫⁻ t in
            (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
              Ico (k : ℝ) ((k : ℝ) + 1),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)) := by
  let cash : ℕ → Ω → ℝ := fun k ω =>
    (∫⁻ t in
      (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
        Ico (k : ℝ) ((k : ℝ) + 1),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  have hCash : ∀ k : ℕ, Measurable (cash k) := by
    intro k
    exact ENNReal.measurable_toReal.comp
      (AvramDividend.Classical.stopped_discounted_unit_cash_measurable_of_strategy
        X q x D hD T k)
  have hPrefix : ∀ n : ℕ, Measurable
      (fun ω : Ω => ∑ k ∈ Finset.range n, cash k ω) := by
    intro n
    induction n with
    | zero =>
        simpa using (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))
    | succ n ih =>
        have hAdd : Measurable (fun ω : Ω =>
            (∑ k ∈ Finset.range n, cash k ω) + cash n ω) :=
          ih.add (hCash n)
        simpa only [Finset.sum_range_succ] using hAdd
  intro n
  change Measurable (fun ω : Ω =>
    ENNReal.ofReal (∑ k ∈ Finset.range n, cash k ω))
  exact ENNReal.measurable_ofReal.comp (hPrefix n)
