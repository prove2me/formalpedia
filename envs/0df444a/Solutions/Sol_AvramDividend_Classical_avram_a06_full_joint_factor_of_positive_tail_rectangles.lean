-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_full_joint_factor_of_positive_tail_rectangles
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:26:16.039913+00:00
-- url     : https://prove2.me/submissions/14669c99-5339-41fe-812c-2c52c23a0ba1

import Mathlib.Probability.ConditionalProbability
import Theorems.Thm_AvramDividend_Classical_avram_a06_finite_real_measures_eq_of_Ioi
import Theorems.Thm_AvramDividend_Classical_avram_a06_real_rectangles_factor_of_positive_tails
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
noncomputable section

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
    (D : Set (ℝ × E)) (hD : MeasurableSet D) :
    P {ω | ω ∈ H ∧ (R ω, F ω) ∈ D} =
      P H * P {ω | (R ω, F ω) ∈ D} := by
  let J : Ω → ℝ × E := fun ω => (R ω, F ω)
  have hJ : Measurable J := hR.prodMk hF
  have heq : (P.restrict H).map J = (P H) • P.map J := by
    apply Measure.ext_prod
    intro A B hA hB
    have hAB : MeasurableSet (A ×ˢ B) := hA.prod hB
    have hfactor :=
      AvramDividend.Classical.avram_a06_real_rectangles_factor_of_positive_tails
        R hR F hF H hH hPos hTail A hA B hB
    calc
      ((P.restrict H).map J) (A ×ˢ B) =
          P {ω | ω ∈ H ∧ R ω ∈ A ∧ F ω ∈ B} := by
        rw [Measure.map_apply hJ hAB, Measure.restrict_apply (hJ hAB)]
        congr 1
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod,
          J, Set.mem_setOf_eq]
        tauto
      _ = P H * P {ω | R ω ∈ A ∧ F ω ∈ B} := hfactor
      _ = ((P H) • P.map J) (A ×ˢ B) := by
        rw [Measure.smul_apply, Measure.map_apply hJ hAB]
        congr 1
  have hDpre : MeasurableSet (J ⁻¹' D) := hJ hD
  have h := congrArg (fun μ : Measure (ℝ × E) => μ D) heq
  rw [Measure.map_apply hJ hD, Measure.restrict_apply hDpre,
    Measure.smul_apply, Measure.map_apply hJ hD] at h
  have hL : J ⁻¹' D ∩ H = {ω | ω ∈ H ∧ (R ω, F ω) ∈ D} := by
    ext ω
    simp [J, and_comm]
  have hR' : J ⁻¹' D = {ω | (R ω, F ω) ∈ D} := rfl
  rw [hL, hR'] at h
  exact h
