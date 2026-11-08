-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_turn11_initial_filtration_ae_martingale_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T00:16:40.935089+00:00
-- url     : https://prove2.me/submissions/eb083aaa-97e6-4bf6-8d3e-31b9fab57509

import Mathlib.Probability.Process.Filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Almost-everywhere martingale domination yields a budget simultaneously on
every event observable at the initial filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (b : ℝ) (F M : Ω → ℝ)
    (hFI : Integrable F P) (hMI : Integrable M P)
    (hCondZero : ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0)
    (hUpper : ∀ᵐ ω ∂P, F ω ≤ b + M ω) :
    ∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal := by
  intro A hA0
  have hm : 𝓕.rightCont 0 ≤ mΩ := (𝓕.rightCont).le 0
  have hA : MeasurableSet A := hm A hA0
  have hMzero : (∫ ω in A, M ω ∂P) = 0 := by
    have hCondInt := setIntegral_condExp hm hMI hA0
    calc
      (∫ ω in A, M ω ∂P) =
          ∫ ω in A, condExp (𝓕.rightCont 0) P M ω ∂P :=
            hCondInt.symm
      _ = ∫ _ in A, (0 : ℝ) ∂P := by
        apply setIntegral_congr_ae hA
        filter_upwards [hCondZero] with ω hzero hω
        exact hzero
      _ = 0 := by simp
  have hAddI : Integrable (fun ω => b + M ω) P :=
    (integrable_const b).add hMI
  have hLe : (∫ ω in A, F ω ∂P) ≤
      ∫ ω in A, b + M ω ∂P :=
    setIntegral_mono_ae hFI.integrableOn hAddI.integrableOn hUpper
  calc
    (∫ ω in A, F ω ∂P) ≤ ∫ ω in A, b + M ω ∂P := hLe
    _ = (∫ _ in A, b ∂P) + (∫ ω in A, M ω ∂P) := by
      exact integral_add (integrable_const b).integrableOn hMI.integrableOn
    _ = b * (P A).toReal := by
      rw [hMzero, add_zero, setIntegral_const]
      simp [smul_eq_mul, Measure.real, mul_comm]
