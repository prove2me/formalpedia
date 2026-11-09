-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed11_mean_to_signed_of_expected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T08:31:32.794916+00:00
-- url     : https://prove2.me/submissions/cc1d5383-559e-4225-b72a-2ac9aef4fcb7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_expected_budget_witness_of_original_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Z : Ω → ℝ) (hZI : Integrable Z P) (b : ℝ)
    (hBudget : (∫ ω, Z ω ∂P) ≤ b) :
    ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧ (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        Z ω ≤ b + Mc ω + Ms ω + Ml ω + G ω + R ω) := by
  have hZero : Integrable (fun _ : Ω => (0 : ℝ)) P := by simp
  have hBudget' :
      (∫ ω, Z ω + (0 : ℝ) ∂P) ≤ (fun _ : ℝ => b) 0 := by
    simpa using hBudget
  obtain ⟨M, G₀, H₀, hMI, hGI, hHI, hM0, hGH, hSrc⟩ :=
    avram_p4_f_assembly_expected_budget_witness_of_original_L1
      X (fun _ : ℝ => b) 0 Z (fun _ : Ω => 0) hZI hZero hBudget'
  refine ⟨M, (fun _ => 0), (fun _ => 0), (fun _ => 0),
    (fun ω => G₀ ω + H₀ ω), hMI, ?_, ?_, hM0, ?_, ?_, ?_, hGH, ?_⟩
  · simp
  · simp
  · simp
  · simp
  · simp
  · filter_upwards [hSrc] with ω hω
    linarith
