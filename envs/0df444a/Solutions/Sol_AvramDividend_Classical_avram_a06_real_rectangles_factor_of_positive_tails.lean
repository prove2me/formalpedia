-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_real_rectangles_factor_of_positive_tails
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:12:03.931277+00:00
-- url     : https://prove2.me/submissions/8b6c43fd-c943-48a5-b9b1-f13dc4e31d89

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Theorems.Thm_AvramDividend_Classical_avram_a06_finite_real_measures_eq_of_Ioi
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

private theorem a06_zero_from_positive
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (R : Ω → ℝ) (F : Ω → E) (H : Set Ω)
    (hPos : ∀ᵐ ω ∂P, 0 < R ω) (B : Set E)
    (hZero : P {ω | ω ∈ H ∧ 0 < R ω ∧ F ω ∈ B} =
      P H * P {ω | 0 < R ω ∧ F ω ∈ B}) :
    P (H ∩ {ω | F ω ∈ B}) = P H * P {ω | F ω ∈ B} := by
  let S : Set Ω := {ω | F ω ∈ B}
  calc
    P (H ∩ S) = P {ω | ω ∈ H ∧ 0 < R ω ∧ F ω ∈ B} := by
      apply measure_congr
      filter_upwards [hPos] with ω hp
      exact propext (show (ω ∈ H ∧ F ω ∈ B) ↔ (ω ∈ H ∧ 0 < R ω ∧ F ω ∈ B) from by tauto)
    _ = P H * P {ω | 0 < R ω ∧ F ω ∈ B} := hZero
    _ = P H * P S := by
      congr 1
      apply measure_congr
      filter_upwards [hPos] with ω hp
      exact propext (show (0 < R ω ∧ F ω ∈ B) ↔ (F ω ∈ B) from by tauto)

private theorem a06_all_tails
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (R : Ω → ℝ) (F : Ω → E) (H : Set Ω)
    (hPos : ∀ᵐ ω ∂P, 0 < R ω)
    (hTail : ∀ u : ℝ, 0 ≤ u → ∀ B : Set E,
      MeasurableSet B →
      P {ω | ω ∈ H ∧ u < R ω ∧ F ω ∈ B} =
        P H * P {ω | u < R ω ∧ F ω ∈ B})
    (B : Set E) (hB : MeasurableSet B) (u : ℝ) :
    P {ω | ω ∈ H ∧ u < R ω ∧ F ω ∈ B} =
      P H * P {ω | u < R ω ∧ F ω ∈ B} := by
  by_cases hu : 0 ≤ u
  · exact hTail u hu B hB
  · have hn : u < 0 := lt_of_not_ge hu
    calc
      P {ω | ω ∈ H ∧ u < R ω ∧ F ω ∈ B} =
        P {ω | ω ∈ H ∧ 0 < R ω ∧ F ω ∈ B} := by
          apply measure_congr
          filter_upwards [hPos] with ω hp
          have huω : u < R ω := lt_trans hn hp
          exact propext (show (ω ∈ H ∧ u < R ω ∧ F ω ∈ B) ↔
            (ω ∈ H ∧ 0 < R ω ∧ F ω ∈ B) from by tauto)
      _ = P H * P {ω | 0 < R ω ∧ F ω ∈ B} :=
        hTail 0 le_rfl B hB
      _ = P H * P {ω | u < R ω ∧ F ω ∈ B} := by
        congr 1
        apply measure_congr
        filter_upwards [hPos] with ω hp
        have huω : u < R ω := lt_trans hn hp
        exact propext (show (0 < R ω ∧ F ω ∈ B) ↔
          (u < R ω ∧ F ω ∈ B) from by tauto)

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (R : Ω → ℝ) (hR : Measurable R)
    (F : Ω → E) (hF : Measurable F)
    (H : Set Ω) (hH : MeasurableSet H)
    (hPos : ∀ᵐ ω ∂P, 0 < R ω)
    (hTail : ∀ (u : ℝ), 0 ≤ u → ∀ (B : Set E),
      MeasurableSet B →
      P {ω | ω ∈ H ∧ u < R ω ∧ F ω ∈ B} =
        P H * P {ω | u < R ω ∧ F ω ∈ B})
    (A : Set ℝ) (hA : MeasurableSet A)
    (B : Set E) (hB : MeasurableSet B) :
    P {ω | ω ∈ H ∧ R ω ∈ A ∧ F ω ∈ B} =
      P H * P {ω | R ω ∈ A ∧ F ω ∈ B} := by
  let S : Set Ω := {ω | F ω ∈ B}
  have hS : MeasurableSet S := hF hB
  have hzero := a06_zero_from_positive R F H hPos B (hTail 0 le_rfl B hB)
  have hall := a06_all_tails R F H hPos hTail B hB
  let μ : Measure ℝ := (P.restrict (H ∩ S)).map R
  let ν : Measure ℝ := (P H) • (P.restrict S).map R
  have hmass : μ Set.univ = ν Set.univ := by
    simpa [μ, ν, S, Measure.map_apply hR MeasurableSet.univ,
      Measure.restrict_apply, Set.inter_comm] using hzero
  haveI : IsFiniteMeasure ν := ⟨by
    rw [← hmass]
    exact measure_lt_top μ Set.univ⟩
  have heq : μ = ν := by
    apply AvramDividend.Classical.avram_a06_finite_real_measures_eq_of_Ioi
    · exact hmass
    · intro u
      have hh := hall u
      simpa [μ, ν, S, Measure.map_apply hR measurableSet_Ioi,
        Measure.restrict_apply (hR measurableSet_Ioi),
        Set.inter_def, and_assoc, and_comm, and_left_comm] using hh
  have h := congrArg (fun m : Measure ℝ => m A) heq
  have hs : (R ⁻¹' A) ∩ (H ∩ S) = {ω | ω ∈ H ∧ R ω ∈ A ∧ F ω ∈ B} := by
    ext ω; simp only [S, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]; tauto
  have ht : (R ⁻¹' A) ∩ S = {ω | R ω ∈ A ∧ F ω ∈ B} := by
    ext ω; simp only [S, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
  simpa only [μ, ν, Measure.map_apply hR hA, Measure.smul_apply,
    Measure.restrict_apply (hR hA), hs, ht, smul_eq_mul] using h
