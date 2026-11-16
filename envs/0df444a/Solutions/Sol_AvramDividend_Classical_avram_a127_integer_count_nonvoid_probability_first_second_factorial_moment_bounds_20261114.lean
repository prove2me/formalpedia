-- Prove2me | solution 1 for AvramDividend.Classical.avram_a127_integer_count_nonvoid_probability_first_second_factorial_moment_bounds_20261114
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:36:53.15906+00:00
-- url     : https://prove2.me/submissions/a5a09558-5588-4fa2-9593-be9bf03d0d95

import Mathlib
open MeasureTheory Filter Set Topology
open scoped ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (hFirst : Integrable (fun ω => (K ω : ℝ)) P)
    (hSecond : Integrable (fun ω => (K ω : ℝ) ^ 2) P) :
    let mean : ℝ := ∫ ω, (K ω : ℝ) ∂P
    let second : ℝ := ∫ ω, (K ω : ℝ) ^ 2 ∂P
    mean - (second - mean) ≤
      1 - (P {ω : Ω | K ω = 0}).toReal ∧
      1 - (P {ω : Ω | K ω = 0}).toReal ≤ mean := by
  intro mean second
  set A : Set Ω := {ω : Ω | K ω = 0} with hAdef
  have hA : MeasurableSet A := hK (measurableSet_singleton 0)
  set f : Ω → ℝ := Aᶜ.indicator (1 : Ω → ℝ) with hfdef
  have hfint : Integrable f P := (integrable_const (1 : ℝ)).indicator hA.compl
  have hf : ∫ ω, f ω ∂P = 1 - (P A).toReal := by
    rw [hfdef, integral_indicator_one hA.compl, measureReal_def,
      prob_compl_eq_one_sub hA, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
    simp
  have hpt : ∀ ω, (2 * (K ω : ℝ) - (K ω : ℝ) ^ 2) ≤ f ω ∧ f ω ≤ (K ω : ℝ) := by
    intro ω
    by_cases h : K ω = 0
    · have hmem : ω ∉ Aᶜ := by simp [hAdef, h]
      simp [hfdef, Set.indicator_of_notMem hmem, h]
    · have hmem : ω ∈ Aᶜ := by simp [hAdef, h]
      have h1 : (1 : ℝ) ≤ K ω := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
      rw [hfdef, Set.indicator_of_mem hmem, Pi.one_apply]
      constructor
      · nlinarith [sq_nonneg ((K ω : ℝ) - 1)]
      · exact h1
  have hlow : ∫ ω, (2 * (K ω : ℝ) - (K ω : ℝ) ^ 2) ∂P ≤ ∫ ω, f ω ∂P :=
    integral_mono ((hFirst.const_mul 2).sub hSecond) hfint (fun ω => (hpt ω).1)
  have hupp : ∫ ω, f ω ∂P ≤ ∫ ω, (K ω : ℝ) ∂P :=
    integral_mono hfint hFirst (fun ω => (hpt ω).2)
  have hlin : ∫ ω, (2 * (K ω : ℝ) - (K ω : ℝ) ^ 2) ∂P = 2 * mean - second := by
    rw [integral_sub (hFirst.const_mul 2) hSecond, integral_const_mul]
  rw [hf] at hlow hupp
  constructor
  · rw [hlin] at hlow; linarith
  · exact hupp
