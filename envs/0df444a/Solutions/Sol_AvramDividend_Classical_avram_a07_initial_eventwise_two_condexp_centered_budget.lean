-- Prove2me | solution 1 for AvramDividend.Classical.avram_a07_initial_eventwise_two_condexp_centered_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:31:57.795558+00:00
-- url     : https://prove2.me/submissions/90ef4eef-cd7e-4e71-a199-8459857a68a7

import Mathlib.Probability.Process.Filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (b : ℝ) (F MG MJ : Ω → ℝ)
    (hFI : Integrable F P) (hMGI : Integrable MG P)
    (hMJI : Integrable MJ P)
    (hMG0 : ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P MG ω = 0)
    (hMJ0 : ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P MJ ω = 0)
    (hUpper : ∀ᵐ ω ∂P, F ω ≤ b + MG ω + MJ ω) :
    ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal := by
  intro A hA
  have hZeroIntegral (M : Ω → ℝ) (hMI : Integrable M P)
      (hCond : ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0) :
      (∫ ω in A, M ω ∂P) = 0 := by
    calc
      (∫ ω in A, M ω ∂P) =
          ∫ ω in A, condExp (𝓕.rightCont 0) P M ω ∂P :=
        (setIntegral_condExp (𝓕.rightCont.le 0) hMI hA).symm
      _ = 0 := integral_eq_zero_of_ae (ae_restrict_of_ae hCond)
  have hMGzero := hZeroIntegral MG hMGI hMG0
  have hMJzero := hZeroIntegral MJ hMJI hMJ0
  have hconst : Integrable (fun _ : Ω => b) P := integrable_const b
  have hsum : Integrable (fun ω => b + MG ω) P :=
    hconst.add hMGI
  calc
    (∫ ω in A, F ω ∂P) ≤
        ∫ ω in A, b + MG ω + MJ ω ∂P :=
      setIntegral_mono_ae hFI.integrableOn (hsum.add hMJI).integrableOn
        hUpper
    _ = (∫ ω in A, b + MG ω ∂P) +
        (∫ ω in A, MJ ω ∂P) := by
      rw [integral_add hsum.integrableOn hMJI.integrableOn]
    _ = (∫ ω in A, b ∂P) +
        (∫ ω in A, MG ω ∂P) +
        (∫ ω in A, MJ ω ∂P) := by
      rw [integral_add hconst.integrableOn hMGI.integrableOn]
    _ = (∫ ω in A, b ∂P) := by
      simp [hMGzero, hMJzero]
    _ = b * (P A).toReal := by
      rw [integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ]
      ring
