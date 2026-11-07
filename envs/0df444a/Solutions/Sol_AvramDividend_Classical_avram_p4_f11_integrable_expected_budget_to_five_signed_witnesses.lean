-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f11_integrable_expected_budget_to_five_signed_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:17:39.958194+00:00
-- url     : https://prove2.me/submissions/3c608ebc-a3a5-44a1-8c98-817cd798b0d4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Centre the original law payoff, putting the nonpositive expected shortfall
    in one signed remainder; the remaining compensator slots are zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (a : ℝ)
    (hHI : Integrable H P)
    (hBound : (∫ ω, H ω ∂P) ≤ a) :
    ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧ (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        H ω ≤ a + Mc ω + Ms ω + Ml ω + G ω + R ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let e : ℝ := ∫ ω, H ω ∂P
  let Mc : Ω → ℝ := fun ω => H ω - e
  let Ms : Ω → ℝ := fun _ => 0
  let Ml : Ω → ℝ := fun _ => 0
  let G : Ω → ℝ := fun _ => e - a
  let R : Ω → ℝ := fun _ => 0
  have hMc : Integrable Mc P := hHI.sub (integrable_const e)
  refine ⟨Mc, Ms, Ml, G, R, hMc, integrable_const _, integrable_const _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (∫ ω, H ω - e ∂P) = 0
    rw [integral_sub hHI (integrable_const e)]
    simp [e]
  · change (∫ ω, (0 : ℝ) ∂P) = 0
    simp
  · change (∫ ω, (0 : ℝ) ∂P) = 0
    simp
  · filter_upwards [] with ω
    change e - a ≤ 0
    linarith
  · filter_upwards [] with ω
    exact le_refl (0 : ℝ)
  · filter_upwards [] with ω
    change H ω ≤ a + (H ω - e) + 0 + 0 + (e - a) + 0
    linarith
