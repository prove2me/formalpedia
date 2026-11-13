-- Prove2me | solution 1 for CountingLLL.RandomRAM.fair_independent_tape
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:02:13.46495+00:00
-- url     : https://prove2.me/submissions/eb3f1a63-50a1-464d-8c19-27b2c83ed274

import Definitions.Def_CountingLLL_RandomRAM

open MeasureTheory
open scoped ENNReal
open CountingLLL.RandomRAM

theorem tape_bit_fair (i : ℕ) (b : Bool) :
    tapeMeasure {ω | ω i = b} = (1 / 2 : ℝ≥0∞) := by
  let μ : ℕ → Measure Bool := fun _ =>
    (1 / 2 : ℝ≥0∞) • Measure.dirac false + (1 / 2 : ℝ≥0∞) • Measure.dirac true
  have hμ : ∀ i, IsProbabilityMeasure (μ i) := by
    intro i
    constructor
    simp [μ, ENNReal.inv_two_add_inv_two]

  change Measure.infinitePi μ ((fun ω : Tape => ω i) ⁻¹' {b}) = _
  have h := (measurePreserving_eval_infinitePi μ (hμ := hμ) i).measure_preimage
    (s := {b}) (MeasurableSet.singleton b).nullMeasurableSet
  change Measure.infinitePi μ ((fun ω : Tape => ω i) ⁻¹' {b}) = μ i {b} at h
  rw [h]
  cases b <;> simp [μ]

theorem tape_bits_independent :
    ProbabilityTheory.iIndepFun (fun i (ω : Tape) => ω i) tapeMeasure := by
  let μ : ℕ → Measure Bool := fun _ =>
    (1 / 2 : ℝ≥0∞) • Measure.dirac false + (1 / 2 : ℝ≥0∞) • Measure.dirac true
  have hμ : ∀ i, IsProbabilityMeasure (μ i) := by
    intro i
    constructor
    simp [μ, ENNReal.inv_two_add_inv_two]
  change ProbabilityTheory.iIndepFun (fun i (ω : Tape) => ω i) (Measure.infinitePi μ)
  exact @ProbabilityTheory.iIndepFun_infinitePi ℕ (fun _ => Bool) _
    (fun _ => Bool) _ μ hμ (fun _ b => b) (fun _ => measurable_id)

theorem solution :
    (∀ i : ℕ, ∀ b : Bool, tapeMeasure {ω | ω i = b} = (1 / 2 : ℝ≥0∞)) ∧
    ProbabilityTheory.iIndepFun (fun i (ω : Tape) => ω i) tapeMeasure :=
  ⟨tape_bit_fair, tape_bits_independent⟩
