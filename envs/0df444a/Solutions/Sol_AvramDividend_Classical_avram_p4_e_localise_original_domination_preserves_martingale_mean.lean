-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_domination_preserves_martingale_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:07:08.693939+00:00
-- url     : https://prove2.me/submissions/e8d7a6d5-922f-4063-aa89-f67792fadaa7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open AvramDividend.Classical

/-- Genuine domination and almost sure convergence preserve integrability and zero mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Mk : ℕ → Ω → ℝ) (M B : Ω → ℝ)
    (hMkMeas : ∀ k, AEStronglyMeasurable (Mk k) P)
    (hMMeas : AEStronglyMeasurable M P)
    (hBint : Integrable B P)
    (hBound : ∀ k, ∀ᵐ ω ∂P, ‖Mk k ω‖ ≤ B ω)
    (hLimitBound : ∀ᵐ ω ∂P, ‖M ω‖ ≤ ‖B ω‖)
    (hAs : ∀ᵐ ω ∂P, Tendsto (fun k => Mk k ω) atTop (𝓝 (M ω)))
    (hCentre : ∀ k, (∫ ω, Mk k ω ∂P) = 0) :
    Integrable M P ∧ (∫ ω, M ω ∂P) = 0 := by
  have hMint : Integrable M P := Integrable.mono hBint hMMeas hLimitBound
  have hconv :
      Tendsto (fun k => ∫ ω, Mk k ω ∂P) atTop (𝓝 (∫ ω, M ω ∂P)) :=
    tendsto_integral_of_dominated_convergence B hMkMeas hBint hBound hAs
  have hconst :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (∫ ω, M ω ∂P)) := by
    simpa only [hCentre] using hconv
  have h0 : (0 : ℝ) = ∫ ω, M ω ∂P :=
    tendsto_nhds_unique tendsto_const_nhds hconst
  exact ⟨hMint, h0.symm⟩
