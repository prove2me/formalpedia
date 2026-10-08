-- Prove2me | solution 1 for AvramDividend.Classical.martingale_antitone_weight_supermartingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:10:38.407114+00:00
-- url     : https://prove2.me/submissions/0a2f7df6-fdc0-4edf-9711-6fa61e00ad07

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (f : ℝ≥0 → Ω → ℝ) (hf : Martingale f 𝓕 μ)
    (hpos : ∀ t : ℝ≥0, ∀ᵐ ω ∂μ, 0 ≤ f t ω)
    (c : ℝ≥0 → ℝ) (hc : Antitone c) :
    Supermartingale (fun t ω => c t * f t ω) 𝓕 μ := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact stronglyMeasurable_const.mul (hf.stronglyAdapted t)
  · intro s t hst
    have hconst :
        μ[(fun ω => c t * f t ω) | 𝓕 s] =ᵐ[μ]
          (fun ω => c t * μ[f t | 𝓕 s] ω) := by
      have hfun : (c t) • (f t) =
          (fun ω => c t * f t ω) := by
        funext ω
        simp only [Pi.smul_apply, smul_eq_mul]
      have hfunCE : (c t) • μ[f t | 𝓕 s] =
          (fun ω => c t * μ[f t | 𝓕 s] ω) := by
        funext ω
        simp only [Pi.smul_apply, smul_eq_mul]
      have hsmul :
          μ[(c t) • (f t) | 𝓕 s] =ᵐ[μ]
            (c t) • μ[f t | 𝓕 s] :=
        condExp_smul (c t) (f t) (𝓕 s)
      rw [hfun, hfunCE] at hsmul
      exact hsmul
    filter_upwards [hconst, hf.2 s t hst, hpos s] with ω hconst heq hnonneg
    calc
      μ[(fun ω => c t * f t ω) | 𝓕 s] ω =
          c t * f s ω := by rw [hconst, heq]
      _ ≤ c s * f s ω := mul_le_mul_of_nonneg_right (hc hst) hnonneg
  · intro t
    change Integrable (fun ω => c t * f t ω) μ
    exact (hf.integrable t).const_mul (c t)
