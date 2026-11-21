-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_fullmark_gaussian_eventwise_positive_excess_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T19:01:01.999461+00:00
-- url     : https://prove2.me/submissions/116430aa-e30e-4440-8822-eb00e542955b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (F : Ω → ℝ) (c : ℝ) (hFI : Integrable F P)
    (hApprox : ∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      ∀ ε : ℝ, 0 < ε →
      ∃ (G J : Ω → ℝ),
        IntegrableOn G A P ∧ IntegrableOn J A P ∧
        (∫ ω in A, G ω ∂P) = 0 ∧
        (∫ ω in A, J ω ∂P) = 0 ∧
        IntegrableOn (fun ω => max (F ω - c - G ω - J ω) 0) A P ∧
        (∫ ω in A, max (F ω - c - G ω - J ω) 0 ∂P) ≤ ε) :
    ∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A, F ω ∂P) ≤ c * (P A).toReal := by
  classical
  intro A hA
  by_contra hbudget
  have hgap : 0 < (∫ ω in A, F ω ∂P) - c * (P A).toReal := by
    have hlt : c * (P A).toReal < (∫ ω in A, F ω ∂P) :=
      lt_of_not_ge hbudget
    linarith
  obtain ⟨G, J, hGI, hJI, hGzero, hJzero, hEI, hsmall⟩ :=
    hApprox A hA
      (((∫ ω in A, F ω ∂P) - c * (P A).toReal) / 2) (half_pos hgap)
  have hFA : IntegrableOn F A P := hFI.integrableOn
  have hcI : IntegrableOn (fun _ : Ω => c) A P :=
    (integrable_const c).integrableOn
  have hFc : IntegrableOn (fun ω => F ω - c) A P := hFA.sub hcI
  have hFcG : IntegrableOn (fun ω => F ω - c - G ω) A P :=
    hFc.sub hGI
  have hD : IntegrableOn (fun ω => F ω - c - G ω - J ω) A P :=
    hFcG.sub hJI
  have hmono :
      (∫ ω in A, F ω - c - G ω - J ω ∂P) ≤
      (∫ ω in A, max (F ω - c - G ω - J ω) 0 ∂P) := by
    exact integral_mono hD hEI (fun ω => le_max_left _ _)
  have hsplit :
      (∫ ω in A, F ω - c - G ω - J ω ∂P) =
      (∫ ω in A, F ω ∂P) -
      (∫ ω in A, c ∂P) -
      (∫ ω in A, G ω ∂P) -
      (∫ ω in A, J ω ∂P) := by
    rw [integral_sub hFcG hJI, integral_sub hFc hGI,
      integral_sub hFA hcI]
  have hconst : (∫ ω in A, (c : ℝ) ∂P) =
      c * (P A).toReal := by
    simp [integral_const, Measure.real_def,
      Measure.restrict_apply_univ, mul_comm]
  rw [hsplit, hconst, hGzero, hJzero] at hmono
  linarith
