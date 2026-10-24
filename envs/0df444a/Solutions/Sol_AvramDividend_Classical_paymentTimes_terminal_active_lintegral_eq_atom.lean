-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_terminal_active_lintegral_eq_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:00:49.576328+00:00
-- url     : https://prove2.me/submissions/e564419f-543f-44af-8d6a-8d761b37807a

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- When the terminal horizon is a payment time, the exact
    closed-horizon endpoint reward equals its Stieltjes singleton atom. -/
theorem solution
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (σ : ℝ≥0∞) (T : ℝ) (hactive : T ∈ paymentTimes σ) :
    (∫⁻ t in paymentTimes σ ∩ ({T} : Set ℝ), f t ∂μ) =
      f T * μ {T} := by
  have hset : paymentTimes σ ∩ ({T} : Set ℝ) = {T} := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · exact fun ht => ht.2
    · intro ht
      subst t
      exact ⟨hactive, rfl⟩
  rw [hset, lintegral_singleton]
