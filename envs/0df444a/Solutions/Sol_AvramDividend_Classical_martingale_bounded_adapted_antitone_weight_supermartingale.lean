-- Prove2me | solution 1 for AvramDividend.Classical.martingale_bounded_adapted_antitone_weight_supermartingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:29:14.563767+00:00
-- url     : https://prove2.me/submissions/dc3ec890-5769-4828-8b08-fca970090539

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
    (w : ℝ≥0 → Ω → ℝ)
    (hwadapt : Adapted 𝓕 w)
    (hwbdd : ∀ t ω, 0 ≤ w t ω ∧ w t ω ≤ 1)
    (hwanti : ∀ ω, Antitone (fun t => w t ω)) :
    Supermartingale (fun t ω => w t ω * f t ω) 𝓕 μ := by
  have hwsm (t : ℝ≥0) : AEStronglyMeasurable (w t) μ :=
    ((hwadapt t).mono (𝓕.le t) le_rfl).aestronglyMeasurable
  have hwbound (t : ℝ≥0) :
      ∀ᵐ ω ∂μ, ‖w t ω‖ ≤ (1 : ℝ) := by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hwbdd t ω).1]
    exact (hwbdd t ω).2
  have hInt (s t : ℝ≥0) :
      Integrable (fun ω => w s ω * f t ω) μ :=
    (hf.integrable t).bdd_mul (hwsm s) (hwbound s)
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact (hwadapt t).stronglyMeasurable.mul (hf.stronglyAdapted t)
  · intro s t hst
    have hpoint :
        (fun ω => w t ω * f t ω) ≤ᵐ[μ]
        (fun ω => w s ω * f t ω) := by
      filter_upwards [hpos t] with ω hft
      exact mul_le_mul_of_nonneg_right (hwanti ω hst) hft
    have hmonoCE :
        μ[(fun ω => w t ω * f t ω) | 𝓕 s] ≤ᵐ[μ]
          μ[(fun ω => w s ω * f t ω) | 𝓕 s] :=
      condExp_mono (m := 𝓕 s) (hInt t t) (hInt s t) hpoint
    have hpull :=
      condExp_mul_of_aestronglyMeasurable_left
        ((hwadapt s).stronglyMeasurable.aestronglyMeasurable)
        (hInt s t) (hf.integrable t)
    change μ[(fun ω => w s ω * f t ω) | 𝓕 s] =ᵐ[μ]
      (fun ω => w s ω * μ[f t | 𝓕 s] ω) at hpull
    filter_upwards [hmonoCE, hpull, hf.2 s t hst] with ω hm hp heq
    calc
      μ[(fun ω => w t ω * f t ω) | 𝓕 s] ω ≤
          μ[(fun ω => w s ω * f t ω) | 𝓕 s] ω := hm
      _ = w s ω * μ[f t | 𝓕 s] ω := hp
      _ = w s ω * f s ω := by rw [heq]
  · intro t
    exact hInt t t
