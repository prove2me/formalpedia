-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_positive_clock_supported_centered_of_expected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T16:02:42.304487+00:00
-- url     : https://prove2.me/submissions/98b7f14f-5121-499c-a7a9-36c016852ad8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A)
    (F : Ω → ℝ) (hFI : Integrable F P)
    (b : ℝ) (hp : 0 < (P A).toReal)
    (hbudget : (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal) :
    ∃ M : Ω → ℝ,
      Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
      (∀ ω, ω ∉ A → M ω = 0) ∧
      (∀ ω, ω ∈ A → F ω ≤ b + M ω) := by
  classical
  let p : ℝ := (P A).toReal
  let c : ℝ := (b * p - (∫ ω in A, F ω ∂P)) / p
  have hp' : 0 < p := hp
  have hpn : p ≠ 0 := ne_of_gt hp'
  have hc : 0 ≤ c := by
    apply div_nonneg
    · exact sub_nonneg.mpr hbudget
    · exact le_of_lt hp'
  let M : Ω → ℝ := A.indicator (fun ω => F ω - b + c)
  have hMI : Integrable M P :=
    ((hFI.sub (integrable_const b)).add (integrable_const c)).indicator hA
  have hFset : Integrable F (P.restrict A) := hFI.integrableOn
  have hBset : Integrable (fun _ : Ω => b) (P.restrict A) :=
    integrable_const b
  have hCset : Integrable (fun _ : Ω => c) (P.restrict A) :=
    integrable_const c
  have hMInt :
      (∫ ω, M ω ∂P) =
        (∫ ω in A, F ω ∂P) - b * p + c * p := by
    calc
      (∫ ω, M ω ∂P) =
          ∫ ω in A, (F ω - b + c) ∂P := by
            exact integral_indicator hA
      _ = (∫ ω in A, F ω ∂P) - b * p + c * p := by
          calc
            (∫ ω in A, F ω - b + c ∂P) =
                (∫ ω in A, F ω - b ∂P) +
                  (∫ ω in A, (c : ℝ) ∂P) := by
                    exact integral_add (hFset.sub hBset) hCset
            _ = ((∫ ω in A, F ω ∂P) -
                (∫ ω in A, (b : ℝ) ∂P)) +
                  (∫ ω in A, (c : ℝ) ∂P) := by
                    rw [integral_sub hFset hBset]
            _ = (∫ ω in A, F ω ∂P) - b * p + c * p := by
                  simp [p, Measure.real_def, mul_comm]
  have hMean : (∫ ω, M ω ∂P) = 0 := by
    rw [hMInt]
    dsimp [c]
    field_simp
    ring
  refine ⟨M, hMI, hMean, ?_, ?_⟩
  · intro ω hnot
    simp [M, Set.indicator, hnot]
  · intro ω hmem
    have hMval : M ω = F ω - b + c := by
      simp [M, Set.indicator, hmem]
    rw [hMval]
    linarith
