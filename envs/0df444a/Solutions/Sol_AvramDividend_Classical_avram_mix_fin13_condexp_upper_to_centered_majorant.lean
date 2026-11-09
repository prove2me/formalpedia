-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin13_condexp_upper_to_centered_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T22:31:24.466348+00:00
-- url     : https://prove2.me/submissions/4cf2eb39-8355-48bf-a69b-20f2e8cfea71

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- An integrable reward lies below its initial conditional benchmark plus a
    centred integrable residual whenever its conditional mean is bounded. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (F : Ω → ℝ) (hFI : Integrable F P) (b : ℝ)
    (hUpper : ∀ᵐ ω ∂P, condExp G P F ω ≤ b) :
    ∃ M : Ω → ℝ, Integrable M P ∧
      (∀ᵐ ω ∂P, condExp G P M ω = 0) ∧
      (∀ᵐ ω ∂P, F ω ≤ b + M ω) := by
  classical
  let Q : Ω → ℝ := condExp G P F
  have hQI : Integrable Q P := by
    dsimp [Q]
    exact integrable_condExp
  have hSub := condExp_sub hFI hQI G
  have hId : condExp G P Q =ᵐ[P] Q := by
    simpa [Q] using
      (condExp_condExp_of_le (m₁ := G) (m₂ := G) (m₀ := mΩ)
        (μ := P) (f := F) (le_refl G) hG)
  refine ⟨fun ω => F ω - Q ω, hFI.sub hQI, ?_, ?_⟩
  · filter_upwards [hSub, hId] with ω hs hi
    change condExp G P (F - Q) ω = 0
    calc
      condExp G P (F - Q) ω =
          condExp G P F ω - condExp G P Q ω := hs
      _ = 0 := by rw [hi]; simp [Q]
  · filter_upwards [hUpper] with ω hω
    change F ω ≤ b + (F ω - Q ω)
    linarith
