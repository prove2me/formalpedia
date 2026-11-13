-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a54_true_stop_mask_large_source_tail_sum_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:26:14.562383+00:00
-- url     : https://prove2.me/submissions/87d6fd8c-a752-47ad-af9b-228908b8d970

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A genuine stopping mask of finitely many source large-increment energies is measurable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (S : Finset ℕ) (s : ℕ → ℝ≥0)
    (ρ : Ω → ℝ≥0) (hρ : Measurable ρ)
    (Z : ℕ → Ω → ℝ)
    (hZ : ∀ i ∈ S, Measurable (Z i))
    (η : ℝ) :
    Measurable (fun ω : Ω =>
      Finset.sum S (fun i =>
        if s i < ρ ω then
          ENNReal.ofReal (if η ≤ |Z i ω| then (Z i ω)^2 else 0)
        else 0)) := by
  classical
  apply Finset.measurable_sum
  intro i hi
  have hZi : Measurable (Z i) := hZ i hi
  have hEvent : MeasurableSet {ω : Ω | η ≤ |Z i ω|} :=
    measurableSet_le measurable_const hZi.abs
  have hReal : Measurable (fun ω : Ω =>
      if η ≤ |Z i ω| then (Z i ω)^2 else 0) :=
    Measurable.ite hEvent (hZi.pow_const 2) measurable_const
  have hTail : Measurable (fun ω : Ω =>
      ENNReal.ofReal (if η ≤ |Z i ω| then (Z i ω)^2 else 0)) :=
    ENNReal.measurable_ofReal.comp hReal
  exact Measurable.ite
    (measurableSet_lt measurable_const hρ) hTail measurable_const
