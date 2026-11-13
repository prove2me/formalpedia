-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva66_original_strict_stopped_cash_mesh_error_expected_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T16:40:21.99463+00:00
-- url     : https://prove2.me/submissions/6f041e1a-ba10-4cf9-92e7-720a87af4d4b

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger42_original_strict_discounted_cash_mesh_error_L1
import Theorems.Thm_AvramDividend_Classical_avram_gledger80_original_allmesh_strict_cash_error_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0)) :
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 2)
      let F : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      let T : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
            Ioo ((ρ ω : ℝ) - Δ) (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      q * Δ * Real.exp (q * (n : ℝ)) * F + T
    (∀ m : ℕ, Integrable (E m) P) ∧
    Tendsto (fun m => ∫ ω, E m ω ∂P) atTop (nhds (0 : ℝ)) := by
  dsimp only
  let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 2)
      let F : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      let T : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
            Ioo ((ρ ω : ℝ) - Δ) (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      q * Δ * Real.exp (q * (n : ℝ)) * F + T
  change (∀ m : ℕ, Integrable (E m) P) ∧
    Tendsto (fun m => ∫ ω, E m ω ∂P) atTop (nhds (0 : ℝ))
  constructor
  · exact avram_gledger80_original_allmesh_strict_cash_error_integrable
      X hX x C D hD q hq n hn ρ hρstop hρbound
  · have hSmall :=
      avram_gledger42_original_strict_discounted_cash_mesh_error_L1
        X hX x C D hD q hq n hn ρ hρstop hρbound
    have hNonneg (m : ℕ) (ω : Ω) : 0 ≤ E m ω := by
      dsimp only [E]
      positivity
    have hMeanNonneg (m : ℕ) :
        0 ≤ ∫ ω, E m ω ∂P :=
      integral_nonneg (fun ω => hNonneg m ω)
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨k, hk⟩ := hSmall (ε / 2) (by linarith)
    refine ⟨k, ?_⟩
    intro m hm
    have hUpper := (hk m hm).2
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hMeanNonneg m)]
    linarith

