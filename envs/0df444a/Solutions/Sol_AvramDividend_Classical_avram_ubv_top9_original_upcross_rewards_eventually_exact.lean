-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_original_upcross_rewards_eventually_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:39:35.297882+00:00
-- url     : https://prove2.me/submissions/216b65e8-0bc1-4c60-bc33-168788de3b26

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_any_clock_upcross_localisation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Eventually exact original source stopped rewards on true upper-exit clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℝ≥0)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ n)
    (x q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
          else riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    ∃ (κ : ℕ → Ω → ℝ≥0) (H : ℕ → Ω → ℝ),
      (∀ j, IsStoppingTime 𝓕.rightCont
        (fun ω => (κ j ω : WithTop ℝ≥0))) ∧
      (∀ j ω, κ j ω ≤ ρ ω) ∧
      (∀ j ω, X.X (κ j ω) ω ≤ (j : ℝ) + 1) ∧
      (∀ j ω, H j ω =
        Real.exp (-(q * (κ j ω : ℝ))) *
          w (if κ j ω = 0 ∨ (κ j ω : ℝ≥0∞) < ruinTime X x D ω then
              x + X.X (κ j ω) ω - rightLimit D (κ j ω) ω
            else riskProcess X x D (κ j ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) ∧
      (∀ ω, ∀ᶠ j : ℕ in atTop, H j ω = F ω) := by
  classical
  obtain ⟨κ, hStop, hLe, hBound, hEventually⟩ :=
    avram_ubv_top9_original_any_clock_upcross_localisation
      X n ρ hρstop hρle
  let H : ℕ → Ω → ℝ := fun j ω =>
    Real.exp (-(q * (κ j ω : ℝ))) *
      w (if κ j ω = 0 ∨ (κ j ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (κ j ω) ω - rightLimit D (κ j ω) ω
        else riskProcess X x D (κ j ω) ω) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  refine ⟨κ, H, hStop, hLe, hBound, ?_, ?_⟩
  · intro j ω
    rfl
  · intro ω
    filter_upwards [hEventually ω] with j hj
    simpa only [H, hj] using (hFsource ω).symm
